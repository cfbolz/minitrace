import z3
import pytest
from hypothesis import given, strategies, example, seed, assume, settings

from dataclasses import dataclass
from typing import Optional, Any


# start an abstract value that uses "known bits"

@dataclass(eq=False)
class OptInfo:
    """ An abstract domain representing sets of integers where some bits of the
    integer can be known 0, or known 1, the rest is unknown. We represent this
    by two ints:
    - ones, which has 1 bits in the places where the bit must be 1
    - zeros which has 0 bits in the places where the bit must be 0
    every bit can be in one of three states, 0, 1, or ?. the fourth
    combination, where both ones=1 and zeros=0 in the same place, is forbidden.
    """
    zeros : int = -1
    ones : int = 0
    s_mask : int = 0 # mask bit is 1 if value bit matches msb

    def __post_init__(self):
        if isinstance(self.ones, int):
            assert self.is_well_formed()

    def is_well_formed(self):
        # - a bit cannot be both 1 and 0
        # - also, s_mask is not positive (the highest bit must always be set, because
        # it is equal to itself. we also allow zero for "the sign bit
        # infinitely far to the left" in the arbitrary precision formulation of
        # this)
        # - s_mask also needs to all ones, followed by all zeros (ie if you
        # bitflip it, and add 1, you get a power of 2)        
        pow2 = ~self.s_mask + 1
        return (self.ones & ~self.zeros == 0) & (self.s_mask <= 0) & (pow2 & (pow2 - 1) == 0)

    @staticmethod
    def from_constant(const : int):
        """ Construct a OptInfo corresponding to a constant, where all bits
        are known."""
        return OptInfo(const, const)

    @staticmethod
    def from_str(s):
        """ Construct a OptInfo instance that from a string. String can start
        with ...1 to mean that all higher bits are 1, or ...? to mean that all
        higher bits are unknown. Otherwise it is assumed that the higher bits
        are all 0. """
        s, middle, s_mask_s = s.partition(" with s_mask=")
        if middle:
            s_mask = eval(s_mask_s)
        else:
            s_mask = 0
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
            else:
                assert c == '0'
        return OptInfo.from_ones_unknowns(ones, unknowns, s_mask)

    @staticmethod
    def from_ones_unknowns(ones, unknowns, s_mask=0):
        zeros = ones ^ unknowns
        return OptInfo(zeros, ones, s_mask)

    @staticmethod
    def all_unknown():
        """ convenience constructor for the "all bits unknown" abstract value
        """
        return OptInfo.from_str("...?")

    @property
    def unknowns(self):
        """ return an integer where the places that are unknown have a bit
        set. """
        # it's a 0 if it is known, but not 1
        return self.zeros ^ self.ones

    @property
    def knowns(self):
        """ return an integer where the known bits are set. """
        # the knowns are just the unknowns, inverted
        return ~self.unknowns

    def is_constant(self):
        """ Check if the OptInfo instance represents a constant. """
        # it's a constant if there are no unknowns
        return self.unknowns == 0

    def __repr__(self):
        if self.s_mask == 0:
            if self.is_constant():
                return f"OptInfo.from_constant({self.ones})"
            return f"OptInfo({self.zeros}, {self.ones})"
        return f"OptInfo({self.zeros}, {self.ones}, {self.s_mask})"

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
        return "".join(res) + ("" if self.s_mask == 0 else f" with s_mask=-0x{abs(self.s_mask):x}")

    def contains(self, value : int):
        """ Check whether the OptInfo instance contains the concrete integer
        `value`. """
        # check whether value matches the bit pattern. in the places where we
        # know the bits, the value must agree with ones.
        s_masked = value & self.s_mask
        return (value & self.knowns == self.ones) & ((s_masked == 0) | (s_masked == self.s_mask))

    def abstract_invert(self):
        return OptInfo(~self.ones, ~self.zeros)

    def abstract_and(self, other):
        ones = self.ones & other.ones
        zeros = self.zeros & other.zeros
        s_mask = self.s_mask & other.s_mask
        return OptInfo(zeros, ones, s_mask)

    def abstract_or(self, other):
        ones = self.ones | other.ones
        zeros = self.zeros | other.zeros
        s_mask = self.s_mask & other.s_mask
        return OptInfo(zeros, ones, s_mask)

    def abstract_add(self, other):
        sum_ones = self.ones + other.ones
        sum_unknowns = self.unknowns + other.unknowns
        all_carries = sum_ones + sum_unknowns
        ones_carries = all_carries ^ sum_ones
        unknowns = self.unknowns | other.unknowns | ones_carries
        ones = sum_ones & ~unknowns
        zeros = ones ^ unknowns

        s_mask = (self.s_mask & other.s_mask) << 1
        return OptInfo(zeros, ones, s_mask)

    def abstract_sub(self, other):
        diff_ones = self.ones - other.ones
        val_borrows = (diff_ones + self.unknowns) ^ (diff_ones - other.unknowns)
        unknowns = self.unknowns | other.unknowns | val_borrows
        ones = diff_ones & ~unknowns

        s_mask = (self.s_mask & other.s_mask) << 1
        return OptInfo.from_ones_unknowns(ones, unknowns, s_mask)

    def abstract_eq(self, other):
        # the result is a 0, 1, or ?

        # if they are both the same constant, they must be equal
        if self.is_constant() and other.is_constant() and self.ones == other.ones:
            return OptInfo.from_constant(1)
        # check whether we have known disagreeing bits, then we know the result
        # is 0
        if self._disagrees(other):
            return OptInfo.from_constant(0)
        return OptInfo.from_ones_unknowns(0, 1) # an unknown boolean

    def _disagrees(self, other):
        # check whether the bits disagree in any place where both are known
        both_known = self.knowns & other.knowns
        return self.ones & both_known != other.ones & both_known

    def nonnegative(self):
        return (self.ones | self.unknowns) >= 0

    def is_and_identity(self, other):
        """ Return True if n1 & n2 == n1 for any n1 in self and n2 in other.
        (or, equivalently, return True if n1 | n2 == n2)"""
        # for a single bit: x & 1 == x
        #                   0 & anything == 0
        # for or:           1 | anything == 1
        #                   x | 0 == x
        return other.ones | ~self.zeros == -1



# unit tests

def test_str():
    assert str(OptInfo.from_constant(0)) == '0'
    assert str(OptInfo.from_constant(5)) == '101'
    assert str(OptInfo.from_ones_unknowns(0b101, 0b10)) == '1?1'
    assert str(OptInfo.from_ones_unknowns(~0b1111, 0b10)) == '...100?0'
    assert str(OptInfo.from_ones_unknowns(1, ~0b1)) == '...?1'

def test_from_str():
    assert OptInfo.from_str('0')
    assert str(OptInfo.from_constant(5)) == '101'
    assert str(OptInfo.from_ones_unknowns(0b101, 0b10)) == '1?1'
    assert str(OptInfo.from_ones_unknowns(~0b1111, 0b10)) == '...100?0'
    assert str(OptInfo.from_ones_unknowns(1, ~0b1)) == '...?1'

    x = OptInfo.from_str('...?00 with s_mask=-0x100')
    assert x.zeros == ~0b11
    assert x.ones == 0
    assert x.s_mask == -0x100



def test_contains():
    k1 = OptInfo.from_str('1?1')
    assert k1.contains(0b111)
    assert k1.contains(0b101)
    assert not k1.contains(0b110)
    assert not k1.contains(0b011)

    k2 = OptInfo.from_str('...?1') # all odd numbers
    for i in range(-101, 100):
        assert k2.contains(i) == (i & 1)

def test_contains_smask():
    k1 = OptInfo(s_mask=-1)
    # 0 or all 1, ie -1
    assert k1.contains(0)
    assert k1.contains(-1)
    for i in [1, 2, 3, 4, 100, 100000]:
        assert not k1.contains(i)
    k1 = OptInfo(s_mask=(-1) << 1)
    assert k1.contains(0)
    assert k1.contains(1)
    assert k1.contains(-1)
    assert k1.contains(-2)
    for i in [2, 3, 4, 100, 100000]:
        assert not k1.contains(i)

def test_invert():
    k1 = OptInfo.from_str('01?01?01?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...10?10?10?'

    k1 = OptInfo.from_str('...?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...?'

def test_and():
    # test all combinations of 0, 1, ? in one example
    k1 = OptInfo.from_str('01?01?01?')
    k2 = OptInfo.from_str('000111???')
    res = k1.abstract_and(k2)     # should be: 0...00001?0??
    assert str(res) ==   "1?0??"

def test_and_smask():
    k1 = OptInfo(s_mask=~0b111)
    low_k1, high_h1 = (-2**3, 2**3-1)
    for n1 in range(low_k1, high_h1 + 1):
        assert k1.contains(n1)
    assert not k1.contains(low_k1 - 1)
    assert not k1.contains(high_h1 + 1)
    k2 = OptInfo(s_mask=~0b11111)
    low_k2, high_h2 = (-2**5, 2**5-1)
    for n2 in range(low_k2, high_h2 + 1):
        assert k2.contains(n2)
    assert not k2.contains(low_k2 - 1)
    assert not k2.contains(high_h2 + 1)
    res = k1.abstract_and(k2)     # should be: 0...00001?0??
    assert res.s_mask == ~0b11111
    for n1 in range(low_k1, high_h1 + 1):
        for n2 in range(low_k2, high_h2 + 1):
            assert res.contains(n1 & n2)
    assert not res.contains(low_k2 - 1)
    assert not res.contains(high_h2 + 1)


def test_or():
    k1 = OptInfo.from_str('01?01?01?')
    k2 = OptInfo.from_str('000111???')
    res = k1.abstract_or(k2)     # should be:  0...01?111?1?
    assert str(res) ==   "1?111?1?"

def test_add():
    k1 = OptInfo.from_str('0?10?10?10 with s_mask=-0x100')
    k2 = OptInfo.from_str('0???111000 with s_mask=-0x1000')
    res = k1.abstract_add(k2)
    assert str(res) ==   "?????01?10 with s_mask=-0x2000"

def test_add_smask():
    k1 = OptInfo.from_str('0?10?10?10')
    k2 = OptInfo.from_str('0???111000')
    res = k1.abstract_add(k2)
    assert str(res) ==   "?????01?10"

def test_sub():
    k1 = OptInfo.from_str('0?10?10?10')
    k2 = OptInfo.from_str('0???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "...?11?10"
    k1 = OptInfo.from_str(    '...1?10?10?10')
    k2 = OptInfo.from_str('...10000???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "111?????11?10"


def test_eq():
    k1 = OptInfo.from_str('...?')
    k2 = OptInfo.from_str('...?')
    assert str(k1.abstract_eq(k2)) == '?'
    k1 = OptInfo.from_constant(10)
    assert str(k1.abstract_eq(k1)) == '1'
    k1 = OptInfo.from_constant(10)
    k2 = OptInfo.from_constant(20)
    assert str(k1.abstract_eq(k2)) == '0'


def test_nonnegative():
    k1 = OptInfo.from_str('0?10?10?10')
    assert k1.nonnegative()
    k1 = OptInfo.from_str('...?0')
    assert not k1.nonnegative()
    k1 = OptInfo.from_constant(-1)
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

def build_optinfo_and_contained_number(concrete_value, unknowns):
    return OptInfo.from_ones_unknowns(concrete_value & ~unknowns, unknowns), concrete_value

random_optinfo_and_contained_number = strategies.builds(
    build_optinfo_and_contained_number,
    ints, ints
)

def build_optinfo_and_contained_number_with_smask(concrete_value, unknowns, extra_signed_width):
    # to construct an s_mask, first we compute the tightest s_mask that would
    # contain concrete_value. afterwards we lose extra_signed_width of values by left shift
    s_mask = -1
    while 1:
        if OptInfo(s_mask=s_mask).contains(concrete_value):
            break
        s_mask <<= 1
    res = OptInfo.from_ones_unknowns(concrete_value & ~unknowns, unknowns)
    return OptInfo(res.zeros, res.ones, s_mask << extra_signed_width), concrete_value


random_optinfo_and_contained_number_with_smask = strategies.builds(
    build_optinfo_and_contained_number_with_smask,
    ints, ints, strategies.integers(min_value=0, max_value=INTEGER_WIDTH)
)


constant_optinfo = strategies.builds(
    lambda value: (OptInfo.from_constant(value), value),
    ints
)


optinfo_and_contained_number = constant_optinfo | random_optinfo_and_contained_number | random_optinfo_and_contained_number_with_smask

@given(optinfo_and_contained_number)
def test_hypothesis_contains(t1):
    k1, n1 = t1
    print(OptInfo.from_constant(n1), k1)
    assert k1.contains(n1)

@given(optinfo_and_contained_number)
def test_hypothesis_str_roundtrips(t1):
    k1, n1 = t1
    s = str(k1)
    k2 = OptInfo.from_str(s)
    assert k1.ones == k2.ones
    assert k1.unknowns == k2.unknowns


@given(optinfo_and_contained_number)
def test_hypothesis_invert(t1):
    k1, n1 = t1
    k2 = k1.abstract_invert()
    n2 = ~n1
    assert k2.contains(n2)


@given(optinfo_and_contained_number, optinfo_and_contained_number)
def test_hypothesis_and(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    assert k3.contains(n3)


@given(optinfo_and_contained_number, optinfo_and_contained_number)
def test_hypothesis_or(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    assert k3.contains(n3)


@given(optinfo_and_contained_number, optinfo_and_contained_number)
def test_hypothesis_add(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    assert k3.contains(n3)

@given(optinfo_and_contained_number, optinfo_and_contained_number)
def test_hypothesis_sub(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    assert k3.contains(n3)

@given(optinfo_and_contained_number)
def test_hypothesis_nonnegative(t1):
    k1, n1 = t1
    if n1 < 0:
        assert not k1.nonnegative()

@given(optinfo_and_contained_number, optinfo_and_contained_number)
def test_hypothesis_eq(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_eq(k2)
    assert k3.contains(int(n1 == n2))


# proofs



def BitVec(name):
    return z3.BitVec(name, INTEGER_WIDTH)

def BitVecVal(val):
    return z3.BitVecVal(val, INTEGER_WIDTH)

def z3_setup_variables():
    solver = z3.Solver()

    n1 = BitVec("n1")
    k1 = OptInfo(BitVec("n1_zeros"), BitVec("n1_ones"), BitVec("n1_smask"))
    solver.add(k1.contains(n1))
    solver.add(k1.is_well_formed())

    n2 = BitVec("n2")
    k2 = OptInfo(BitVec("n2_zeros"), BitVec("n2_ones"), BitVec("n2_smask"))
    solver.add(k2.contains(n2))
    solver.add(k2.is_well_formed())
    return solver, k1, n1, k2, n2

def prove(cond, solver):
    z3res = solver.check(z3.Not(cond))
    if z3res != z3.unsat:
        assert z3res == z3.sat # can't be timeout, we set no timeout
        # make the counterexample global, to make inspecting the bug in pdb
        # easier
        global model
        model = solver.model()
        print(f"n1={model.eval(n1)}, n2={model.eval(n2)}")
        counter_example_k1 = OptInfo(model.eval(k1.zeros).as_signed_long(),
                                     model.eval(k1.ones).as_signed_long(),
                                     model.eval(k1.s_mask).as_signed_long())
        counter_example_k2 = OptInfo(model.eval(k2.zeros).as_signed_long(),
                                     model.eval(k2.ones).as_signed_long(),
                                     model.eval(k2.s_mask).as_signed_long())
        print(f"k1={counter_example_k1}, k2={counter_example_k2}")
        print(f"but {cond=} evaluates to {model.eval(cond)}")
        raise ValueError(solver.model())

def test_z3_abstract_invert():
    solver, k1, n1, _, _ = z3_setup_variables()
    k2 = k1.abstract_invert()
    n2 = ~n1
    prove(k2.contains(n2), solver)

def test_z3_abstract_and():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    prove(k3.contains(n3), solver)

def test_z3_abstract_or():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    prove(k3.contains(n3), solver)

def test_z3_abstract_add():
    global solver, k1, n1, k2, n2
    solver, k1, n1, k2, n2 = z3_setup_variables()
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    prove(k3.contains(n3), solver)

def test_z3_abstract_sub():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    prove(k3.contains(n3), solver)

def test_z3_nonnegative():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    prove(
        z3.Implies(
            k1.nonnegative(),
            n1 >= 0,
        ),
        solver
    )

def z3_cond(b, trueval=1, falseval=0):
    return z3.If(b, BitVecVal(trueval), BitVecVal(falseval))

def z3_abstract_eq(k1, k2):
    # follow the *logic* of abstract_eq, we can't call it due to the ifs in it
    case1cond = z3.And(k1.is_constant(), k2.is_constant(), k1.ones == k2.ones)
    case2cond = k1._disagrees(k2)

    # ones is 1 in the first case, 0 otherwise
    ones = z3_cond(case1cond, 1, 0)

    # in the first two cases, unknowns is 0, 1 otherwise
    unknowns = z3_cond(z3.Or(case1cond, case2cond), 0, 1)
    return OptInfo.from_ones_unknowns(ones, unknowns)

def test_z3_abstract_eq_logic():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    n3 = z3_cond(n1 == n2) # concrete result
    k3 = z3_abstract_eq(k1, k2)
    prove(k3.contains(n3), solver)

def test_z3_prove_constant_folding():
    solver, k1, n1, k2, n2 = z3_setup_variables()
    k3 = k1.abstract_invert()
    prove(z3.Implies(k1.is_constant(),
                     k3.is_constant()), solver)

    k3 = k1.abstract_and(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()), solver)

    k3 = k1.abstract_or(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()), solver)

    k3 = k1.abstract_sub(k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()), solver)

    k3 = z3_abstract_eq(k1, k2)
    prove(z3.Implies(z3.And(k1.is_constant(), k2.is_constant()),
                     k3.is_constant()), solver)


@pytest.mark.xfail()
@given(random_optinfo_and_contained_number, random_optinfo_and_contained_number)
@settings(deadline=None)
def test_check_precision(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    # apply transfer function
    k3 = k1.abstract_add(k2)
    example_res = n1 + n2

    # try to find a better version of k3 with Z3
    solver = z3.Solver()
    solver.set("timeout", 8000)

    var1 = BitVec('v1')
    var2 = BitVec('v2')

    ones = BitVec('ones')
    zeros = BitVec('zeros')
    s_mask = BitVec('s_mask')

    concrete = BitVec('concrete')
    better_k3 = OptInfo(zeros, ones, s_mask)
    import gc
    gc.collect()
    print(k1, k2, k3)

    # we're trying to find an example for a better k3, so we use check, without
    # negation:
    res = solver.check(z3.And(
        # better_k3 should be a valid OptInfo instance
        better_k3.is_well_formed(),
        # it should be better than k3, ie there is an element concrete in k3
        # that is not in better_k3
        z3.And(k3.contains(concrete), z3.Not(better_k3.contains(concrete))),
        # now encode the soundness condition for better_k3 with a ForAll:
        # for all concrete values var1 and var2, it must hold that if
        # var1 is in k1 and var2 is in k2 it follows that var1 + var2 is in
        # better_k3
        z3.ForAll(
        [var1, var2],
        z3.Implies(
            z3.And(k1.contains(var1), k2.contains(var2)),
            better_k3.contains(var1 + var2)))))
    # if this query is satisfiable, we have found a better result for the
    # abstract_add
    if res == z3.sat:
        model = solver.model()
        rk3 = OptInfo(model.eval(zeros).as_signed_long(), model.eval(ones).as_signed_long(), model.eval(s_mask).as_signed_long())
        print("better", rk3)
        assert 0
    if res == z3.unknown:
        print("timeout")

