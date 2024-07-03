import z3
import pytest
from hypothesis import given, strategies, example, seed, assume

from dataclasses import dataclass
from typing import Optional, Any

LONG_BIT = 64
MAXINT = 2 ** (LONG_BIT - 1) - 1
MININT = -2 ** (LONG_BIT - 1)

class Value:
    def find(self):
        raise NotImplementedError("abstract")

    def extract(self):
        raise NotImplementedError("abstract")

@dataclass(eq=False)
class Operation(Value):
    name : str
    args : list[Value]

    forwarded : Optional[Value] = None

    info : Any = None

    def find(self) -> Value:
        op = self
        while isinstance(op, Operation):
            next = op.forwarded
            if next is None:
                return op
            op = next
        return op

    def arg(self, index):
        return self.args[index].find()

    def make_equal_to(self, value : Value):
        self.find().forwarded = value

    def extract(self):
        return Operation(self.name, [arg.find for arg in self.args])

    def extract(self):
        raise NotImplementedError("abstract")

@dataclass(eq=False)
class Constant(Value):
    value : object

    def find(self):
        return self

class Block(list):
    def __getattr__(self, opname):
        def wraparg(arg):
            if not isinstance(arg, Value):
                arg = Constant(arg)
            return arg
        def make_op(*args):
            op = Operation(opname,
                [wraparg(arg) for arg in args])
            self.append(op)
            return op
        return make_op

    def emit(self, op):
        self.append(op.extract())
        

def bb_to_str(l : Block, varprefix : str = "var"):
    def arg_to_str(arg : Value):
        if isinstance(arg, Constant):
            return str(arg.value)
        else:
            return varnames[arg]

    varnames = {}
    res = []
    for index, op in enumerate(l):
        # give the operation a name used while
        # printing:
        var =  f"{varprefix}{index}"
        varnames[op] = var
        arguments = ", ".join(
            arg_to_str(op.arg(i))
                for i in range(len(op.args))
        )
        strop = f"{var} = {op.name}({arguments})"
        res.append(strop)
    return "\n".join(res)

def get_num(op, index=1):
    assert isinstance(op.arg(index), Constant)
    return op.arg(index).value

class GuardError(Exception):
    pass

def interpret(bb : Block, *args : tuple[Any]):
    results : dict[Operation, Any] = {}
    def argval(op, i):
        arg = op.arg(i)
        if isinstance(arg, Constant):
            return arg.value
        else:
            assert isinstance(arg, Operation)
            return results[arg]

    for index, op in enumerate(bb):
        if op.name == "getarg":
            res = args[get_num(op, 0)]
        elif op.name == "int_add":
            res = argval(op, 0) + argval(op, 1)
        elif op.name == "int_lt":
            res = int(argval(op, 0) < argval(op, 1))
        elif op.name == "int_and":
            res = argval(op, 0) & argval(op, 1)
        elif op.name == "guard_true":
            res = argval(op, 0)
            if not res:
                raise GuardError(op, res)
        elif op.name == "finish":
            return argval(op, 0)
        else:
            assert 0, "unknown op"
        results[op] = res

def test_interpret():
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.int_lt(0, var0)
    bb.guard_true(var1)
    var2 = bb.int_add(var0, 2)
    var3 = bb.int_lt(2, var2)
    bb.guard_true(var3)
    bb.finish(var2)
    assert interpret(bb, 17) == 19
    assert interpret(bb, 1) == 3
    with pytest.raises(GuardError):
        interpret(bb, -3)


# start an abstract value that uses "known bits"

@dataclass(eq=False)
class KnownBits:
    ones : int
    unknowns : int

    @staticmethod
    def from_constant(const : int):
        return KnownBits(const, 0)

    def is_constant(self):
        return self.unknowns == 0

    def __repr__(self):
        if self.is_constant():
            return f"KnownBits.from_constant({self.ones})"
        return f"KnownBits({self.ones}, {self.unknowns})"

    def __str__(self):
        res = []
        ones, unknowns = self.ones, self.unknowns
        for i in range(LONG_BIT):
            if unknowns & 1:
                res.append('?')
            elif ones & 1:
                res.append('1')
            else:
                res.append('0')
            ones >>= 1
            unknowns >>= 1
            if not ones and not unknowns:
                break
        res.reverse()
        return "".join(res)
            
    def contains(self, value : int):
        return value & ~self.unknowns == self.ones

    def abstract_and(self, other):
        ones = self.ones & other.ones
        unknowns = (self.ones | self.unknowns) & (other.ones | other.unknowns) & ~ones
        return KnownBits(ones, unknowns)

# unit tests

def test_str():
    assert str(KnownBits.from_constant(5)) == '101'
    assert str(KnownBits(5, 0b10)) == '1?1'

def test_and():
    # test all combinations of 0, 1, ? in one example
    k1 = KnownBits(0b010010010, 0b001001001) # 0...01?01?01?
    assert str(k1) == "1?01?01?"
    k2 = KnownBits(0b000111000, 0b000000111) # 0...000111???
    assert str(k2) ==   "111???"
    res = k1.abstract_and(k2)     # should be: 0...00001?0??
    assert str(res) ==   "1?0??"

# hypothesis tests

ints_special = set(range(100))
ints_special = ints_special.union(-x for x in ints_special)
ints_special = ints_special.union(~x for x in ints_special)
ints_special = ints_special.union(1 << i for i in range(LONG_BIT - 2)) # powers of two
ints_special = ints_special.union((1 << i) - 1 for i in range(LONG_BIT - 2)) # powers of two - 1
ints_special = list(ints_special)
ints_special.sort(key=lambda element: (abs(element), element < 0))

ints_special = strategies.sampled_from(
    ints_special)

ints = ints_special | strategies.integers(
        min_value=MININT, max_value=MAXINT)

def build_knownbits_and_contained_number(value, unknowns):
    return KnownBits(value & ~unknowns, unknowns), value

random_knownbits_and_contained_number = strategies.builds(
    build_knownbits_and_contained_number,
    ints, ints
)

constant_knownbits = strategies.builds(
    lambda value: (KnownBits.from_constant(value), value),
    ints
)

knownbits_and_contained_number = constant_knownbits | random_knownbits_and_contained_number

@given(knownbits_and_contained_number)
def test_hypothesis_contains(t1):
    k1, n1 = t1
    print(n1, k1)
    assert k1.contains(n1)


@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_and(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    assert k3.contains(n3)


# proofs



def BitVec(name):
    return z3.BitVec(name, LONG_BIT)

def BitVecVal(val):
    return z3.BitVecVal(val, LONG_BIT)

def z3_knownbits_condition(var, ones, unknowns):
    return var & ~unknowns == ones

def z3_int_info(name):
    ones = BitVec(f"{name}_ones")
    unknowns = BitVec(f"{name}_unknowns")
    info = KnownBits(ones, unknowns)
    var = BitVec(f"{name}_concrete")
    return var, info, z3.And(ones & unknowns == 0, z3_knownbits_condition(var, ones, unknowns))

def prove_implies(*args):
    # the last argument is what is implied
    solver = z3.Solver()
    lhs = z3.And(*args[:-1])
    rhs = args[-1]
    cond = z3.Not(z3.Implies(lhs, rhs))
    res = solver.check(cond)
    if res == z3.unsat:
        return
    else:
        assert res == z3.sat
        raise ValueError(solver.model())

def test_z3_abstract_and():
    selfvar, selfinfo, selfcond = z3_int_info('self')
    othervar, otherinfo, othercond = z3_int_info('other')
    resvar = selfvar & othervar
    resinfo = selfinfo.abstract_and(otherinfo)
    prove_implies(
        selfcond,
        othercond,
        z3_knownbits_condition(resvar, resinfo.ones, resinfo.unknowns)
    )
