import z3
import pytest
from hypothesis import given, strategies, example, seed, assume, settings

from dataclasses import dataclass
from typing import Optional, Any


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


# start an abstract value that uses "known bits"

@dataclass(eq=False)
class KnownBits:
    """ An abstract domain representing sets of integers where some bits of the
    integer can be known 0, or known 1, the rest is unknown. We represent this
    by two ints:
    - ones, which has bits set in the places where the bit must be 1
    - unknowns which has bits set in the places where the bit is unknown
    every bit can be in one of three states, 0, 1, or ?. the fourth
    combination, where both ones and unknowns have a bit set in the same place,
    is forbidden.
    """
    ones : int
    unknowns : int

    def __post_init__(self):
        if isinstance(self.ones, int):
            assert self.is_well_formed()

    def is_well_formed(self):
        # a bit cannot be both 1 and unknown
        return self.ones & self.unknowns == 0

    @staticmethod
    def from_constant(const : int):
        """ Construct a KnownBits corresponding to a constant, where all bits
        are known."""
        return KnownBits(const, 0)

    @staticmethod
    def from_str(s):
        """ Construct a KnownBits instance that from a string. String can start
        with ...1 to mean that all higher bits are 1, or ...? to mean that all
        higher bits are unknown. Otherwise it is assumed that the higher bits
        are all 0. """
        ones, unknowns = 0, 0
        startindex = 0
        if s.startswith("...?"):
            unknowns = -1
            startindex = 4
        elif s.startswith("...1"):
            ones = -1
            startindex = 4
        for index in range(startindex, len(s)):
            ones <<= 1
            unknowns <<= 1
            c = s[index]
            if c == '1':
                ones |= 1
            elif c == '?':
                unknowns |= 1
        return KnownBits(ones, unknowns)

    @property
    def knowns(self):
        """ return an integer where the known bits are set. """
        # the knowns are just the unknowns, inverted
        return ~self.unknowns

    @property
    def zeros(self):
        """ return an integer where the places that are known zeros have a bit
        set. """
        # it's a 0 if it is known, but not 1
        return self.knowns & ~self.ones

    def is_constant(self):
        """ Check if the KnownBits instance represents a constant. """
        # it's a constant if there are no unknowns
        return self.unknowns == 0

    def __repr__(self):
        if self.is_constant():
            return f"KnownBits.from_constant({self.ones})"
        return f"KnownBits({self.ones}, {self.unknowns})"

    def __str__(self):
        res = []
        ones, unknowns = self.ones, self.unknowns
        # construct the string representation right to left
        while 1:
            if not ones and not unknowns:
                break # we leave off the leading known 0s
            if ones == -1 and not unknowns:
                # -1 has all bits set in two's complement, so the leading
                # bits are all 1
                res.append('1')
                res.append("...")
                break
            if unknowns == -1:
                # -1 has all bits set in two's complement, so the leading bits
                # are all ?
                assert not ones
                res.append("?")
                res.append("...")
                break
            if unknowns & 1:
                res.append('?')
            elif ones & 1:
                res.append('1')
            else:
                res.append('0')
            ones >>= 1
            unknowns >>= 1
        if not res:
            res.append('0')
        res.reverse()
        return "".join(res)
            
    def contains(self, value : int):
        """ Check whether the KnownBits instance contains the concrete integer
        `value`. """
        # check whether value matches the bit pattern. in the places where we
        # know the bits, the value must agree with ones.
        return value & self.knowns == self.ones

    def abstract_invert(self):
        return KnownBits(self.zeros, self.unknowns)

    def abstract_and(self, other):
        ones = self.ones & other.ones # known ones
        knowns = self.zeros | other.zeros | ones
        return KnownBits(ones, ~knowns)

    def abstract_or(self, other):
        ones = self.ones | other.ones # known ones
        zeros = self.zeros & other.zeros
        knowns = ones | zeros
        return KnownBits(ones, ~knowns)

    def abstract_add(self, other):
        sum_ones = self.ones + other.ones
        sum_unknowns = self.unknowns + other.unknowns
        all_carries = sum_ones + sum_unknowns
        ones_carries = all_carries ^ sum_ones
        unknowns = self.unknowns | other.unknowns | ones_carries
        ones = sum_ones & ~unknowns
        return KnownBits(ones, unknowns)

    def abstract_sub(self, other):
        diff_ones = self.ones - other.ones
        val_borrows = (diff_ones + self.unknowns) ^ (diff_ones - other.unknowns)
        unknowns = self.unknowns | other.unknowns | val_borrows
        ones = diff_ones & ~unknowns
        return KnownBits(ones, unknowns)

    def abstract_eq(self, other):
        # the result is a 0, 1, or ?

        # can only be known equal if they are both constants
        if self.is_constant() and other.is_constant() and self.ones == other.ones:
            return KnownBits.from_constant(1)
        # check whether we have known disagreeing bits, then we know the result
        # is 0
        if self._disagrees(other):
            return KnownBits.from_constant(0)
        return KnownBits(0, 1) # an unknown boolean

    def _disagrees(self, other):
        # check whether the bits disagree in any place where both are known
        both_known = self.knowns & other.knowns
        return self.ones & both_known != other.ones & both_known

    def nonnegative(self):
        return (self.ones | self.unknowns) >= 0


# unit tests

def test_str():
    assert str(KnownBits.from_constant(0)) == '0'
    assert str(KnownBits.from_constant(5)) == '101'
    assert str(KnownBits(0b101, 0b10)) == '1?1'
    assert str(KnownBits(~0b1111, 0b10)) == '...100?0'
    assert str(KnownBits(1, ~0b1)) == '...?1'

def test_contains():
    k1 = KnownBits.from_str('1?1')
    assert k1.contains(0b111)
    assert k1.contains(0b101)
    assert not k1.contains(0b110)
    assert not k1.contains(0b011)

    k2 = KnownBits.from_str('...?1') # all odd numbers
    for i in range(-101, 100):
        assert k2.contains(i) == (i & 1)

def test_invert():
    k1 = KnownBits.from_str('01?01?01?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...10?10?10?'

    k1 = KnownBits.from_str('...?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...?'

def test_and():
    # test all combinations of 0, 1, ? in one example
    k1 = KnownBits.from_str('01?01?01?')
    k2 = KnownBits.from_str('000111???')
    res = k1.abstract_and(k2)     # should be: 0...00001?0??
    assert str(res) ==   "1?0??"

def test_or():
    k1 = KnownBits.from_str('01?01?01?')
    k2 = KnownBits.from_str('000111???')
    res = k1.abstract_or(k2)     # should be:  0...01?111?1?
    assert str(res) ==   "1?111?1?"

def test_add():
    k1 = KnownBits.from_str('0?10?10?10')
    k2 = KnownBits.from_str('0???111000')
    res = k1.abstract_add(k2)
    assert str(res) ==   "?????01?10"

def test_sub():
    k1 = KnownBits.from_str('0?10?10?10')
    k2 = KnownBits.from_str('0???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "...?11?10"
    k1 = KnownBits.from_str(    '...1?10?10?10')
    k2 = KnownBits.from_str('...10000???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "111?????11?10"


def test_eq():
    k1 = KnownBits.from_str('...?')
    k2 = KnownBits.from_str('...?')
    assert str(k1.abstract_eq(k2)) == '?'
    k1 = KnownBits.from_constant(10)
    assert str(k1.abstract_eq(k1)) == '1'
    k1 = KnownBits.from_constant(10)
    k2 = KnownBits.from_constant(20)
    assert str(k1.abstract_eq(k2)) == '0'


def test_nonnegative():
    k1 = KnownBits.from_str('0?10?10?10')
    assert k1.nonnegative()
    k1 = KnownBits.from_str('...?0')
    assert not k1.nonnegative()
    k1 = KnownBits.from_constant(-1)
    assert not k1.nonnegative()


# hypothesis tests

INTEGER_WIDTH = 64
ints_special = set(range(100))
ints_special = ints_special.union(1 << i for i in range(INTEGER_WIDTH - 2)) # powers of two
ints_special = ints_special.union((1 << i) - 1 for i in range(INTEGER_WIDTH - 2)) # powers of two - 1
ints_special = ints_special.union(-x for x in ints_special)
ints_special = ints_special.union(~x for x in ints_special)
ints_special = list(ints_special)
ints_special.sort(key=lambda element: (abs(element), element < 0))

ints_special = strategies.sampled_from(
    ints_special)

ints = ints_special | strategies.integers()

def build_knownbits_and_contained_number(concrete_value, unknowns):
    return KnownBits(concrete_value & ~unknowns, unknowns), concrete_value

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
    print(KnownBits.from_constant(n1), k1)
    assert k1.contains(n1)

@given(knownbits_and_contained_number)
def test_hypothesis_str_roundtrips(t1):
    k1, n1 = t1
    s = str(k1)
    k2 = KnownBits.from_str(s)
    assert k1.ones == k2.ones
    assert k1.unknowns == k2.unknowns


@given(knownbits_and_contained_number)
def test_hypothesis_invert(t1):
    k1, n1 = t1
    k2 = k1.abstract_invert()
    n2 = ~n1
    assert k2.contains(n2)


@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_and(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    assert k3.contains(n3)


@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_or(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    assert k3.contains(n3)


@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_add(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    assert k3.contains(n3)

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_sub(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    assert k3.contains(n3)

@given(knownbits_and_contained_number)
def test_hypothesis_nonnegative(t1):
    k1, n1 = t1
    if n1 < 0:
        assert not k1.nonnegative()

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_eq(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_eq(k2)
    assert k3.contains(int(n1 == n2))


# proofs



INTEGER_WIDTH = 64

def BitVec(name):
    return z3.BitVec(name, INTEGER_WIDTH)

def BitVecVal(val):
    return z3.BitVecVal(val, INTEGER_WIDTH)

solver = z3.Solver()

n1 = BitVec("n1")
k1 = KnownBits(BitVec("n1_ones"), BitVec("n1_unkowns"))
solver.add(k1.contains(n1))

n2 = BitVec("n2")
k2 = KnownBits(BitVec("n2_ones"), BitVec("n2_unkowns"))
solver.add(k2.contains(n2))

def prove(cond):
    z3res = solver.check(z3.Not(cond))
    if z3res != z3.unsat:
        assert z3res == z3.sat # can't be timeout, we set no timeout
        # make the counterexample global, to make inspecting the bug in pdb
        # easier
        global model 
        model = solver.model()
        print(f"n1={model.eval(n1)}, n2={model.eval(n2)}")
        counter_example_k1 = KnownBits(model.eval(k1.ones).as_signed_long(),
                                       model.eval(k1.unknowns).as_signed_long())
        counter_example_k2 = KnownBits(model.eval(k2.ones).as_signed_long(),
                                       model.eval(k2.unknowns).as_signed_long())
        print(f"k1={counter_example_k1}, k2={counter_example_k2}")
        print(f"but {cond=} evaluates to {model.eval(cond)}")
        raise ValueError(solver.model())

def test_z3_abstract_invert():
    k2 = k1.abstract_invert()
    n2 = ~n1
    prove(k2.contains(n2))

def test_z3_abstract_and():
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    prove(k3.contains(n3))

def test_z3_abstract_or():
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    prove(k3.contains(n3))

def test_z3_abstract_add():
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    prove(k3.contains(n3))

def test_z3_abstract_sub():
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    prove(k3.contains(n3))

def test_z3_nonnegative():
    prove(
        z3.Implies(
            k1.nonnegative(),
            n1 >= 0,
        )
    )

def z3_cond(b, trueval=1, falseval=0):
    return z3.If(b, BitVecVal(trueval), BitVecVal(falseval))

def test_z3_abstract_eq_logic():
    n3 = z3_cond(n1 == n2) # concrete result
    # follow the *logic* of abstract_eq, we can't call it due to the ifs in it
    case1cond = z3.And(k1.is_constant(), k2.is_constant(), k1.ones == k2.ones)
    case2cond = k1._disagrees(k2)

    # ones is 1 in the first case, 0 otherwise
    ones = z3_cond(case1cond, 1, 0)

    # in the first two cases, unknowns is 0, 1 otherwise
    unknowns = z3_cond(z3.Or(case1cond, case2cond), 0, 1)
    k3 = KnownBits(ones, unknowns)
    prove(k3.contains(n3))

def test_z3_prove_constant_folding():
    k3 = k1.abstract_invert()
    prove(z3.Implies(k1.is_constant(),
                     k3.is_constant()))

    k3 = k1.abstract_and(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()))

    k3 = k1.abstract_or(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()))

    k3 = k1.abstract_sub(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()))

@given(random_knownbits_and_contained_number, random_knownbits_and_contained_number)
@settings(deadline=None)
def test_check_precision(t1, t2):
    b1, n1 = t1
    b2, n2 = t2
    b3 = b1.abstract_add(b2)
    example_res = n1 + n2
    ones = BitVec('ones')
    unknowns = BitVec('unknowns')
    solver = z3.Solver()
    solver.set("timeout", 800)
    var1 = BitVec('v1')
    var2 = BitVec('v2')
    formula1 = b1.contains(var1)
    formula2 = b2.contains(var2)

    better_b3 = KnownBits(ones, unknowns)
    import gc
    gc.collect()
    print(b1, b2, b3)

    res = solver.check(z3.And(
        better_b3.is_well_formed(),
        better_b3.knowns & ~b3.knowns != 0,
        better_b3.contains(example_res),
        z3.ForAll(
        [var1, var2],
        z3.Implies(
            z3.And(formula1, formula2),
            better_b3.contains(var1 + var2)))))
    if res == z3.sat:
        model = solver.model()
        rb3 = KnownBits(model.eval(ones).as_signed_long(), model.eval(unknowns).as_signed_long())
        print("better", rb3)
        assert 0
    if res == z3.unknown:
        print("timeout")
    assert res != z3.sat


def test_match():
    class Operation2(Operation):
        __match_args__ = ('name', 'arg0', 'arg1')

        @property
        def arg0(self):
            return self.arg(0)

        @property
        def arg1(self):
            return self.arg(1)

    x = Operation("getarg", [Constant(0)])
    op = Operation2("add", [x, Constant(2)])

    c = Constant(1)
    x.make_equal_to(c)
    match op:
        case Operation2("add", Constant(a), Constant(b)):
            print(a, b)
            assert a 
        case _:
            1/0

    
    x = Operation("getarg", [Constant(0)])
    op1 = Operation2("add", [x, Constant(2)])
    op2 = Operation2("add", [Constant(4), op1])
    match op2:
        case Operation2("add", Constant(c1), Operation2("add", x, Constant(c2))):
            newop = Operation2("add", [x, Constant(c1 + c2)])
        case _:
            newop = op2
    assert newop is not op2

