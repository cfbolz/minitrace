# In this blog post I want to show the complete code (in Python3) of how a very
# simple optimizer for sequences of operations can work. These algorithms could
# be part of a (really simple) compiler, or a JIT.

# https://en.wikipedia.org/wiki/Intermediate_representation

# https://en.wikipedia.org/wiki/Static_single-assignment_form

# The first thing we need to do is define how our operations are stored. The
# format that a compiler uses to store the program while it is being optimized
# is usually called an "intermediate representation" (IR). Many production
# compilers use IRs that are in the Static Single-Assignment Form (SSA). SSA
# form has the property that every variable is assigned to exactly once, and
# every variable is defined before it is used. This simplifies many things.

# Let's make this concrete. If our input program is a complex expressions, such
# as a * (b + 17) + (b + 17) the intermediate representation of that (or at
# least its text representation) would maybe be something like:

# var1 = add(b, 17)
# var2 = mul(a, var1)
# var3 = add(b, 17)
# var4 = add(var2, var3)

# This sequence of instructions is inefficient! The operation add(b, 17) is
# computed twice and we can save time by removing the second one and only
# computing it once. In this post I want to show an optimizer that can do this
# (and some related) optimizations.

# Looking at the IR we notice that the input expression has been linearized
# into a sequence of operations, and all the intermedia results have been given
# unique variable names. The value that every variable is assigned is computed
# by some operation, which consist of an operand and an arbitrary number of
# arguments. The arguments of an operation are either themselves variables or
# constants.

# I will not at all talk about the process of translating the input program
# into the IR. Instead, I will assume we have some component that does this
# translation already. The tests in this blog post will construct small
# snippets of IR by hand. I also won't talk about what happens after the
# optimization (usually the optimized IR is translated into machine code).


# Section 1 the IR

# Let's start modelling some of this with Python classes. First we define a
# base class of all values that can be used as arguments in operations, and
# let's also add a class that represents constants:

# https://en.wikipedia.org/wiki/Control-flow_graph


import pytest
import re
from dataclasses import dataclass
from typing import Optional

class Value:
    pass


@dataclass(eq=False)
class Constant(Value):
    value : object


# One consequence of the fact that every variable is assigned to only once is
# that a variable is in a one-to-one correspondence with the right-hand-side of
# its unique assignment. That means that we don't need a class that represents
# variables at all. Instead, it's sufficient to have a class that represents an
# operation, and that is the same as the variable that it defines:

@dataclass(eq=False)
class Operation(Value):
    name : str
    args : list

    def arg(self, index):
        return self.args[index]

# Now we can instantiate these two classes to represent the example sequence of
# operations above:

def test_construct_example():
    # first we need something to represent "b". In our limited view, we don't
    # know where it comes from, so we will define it with a pseudo-operation
    # called "getarg" which takes a number n as an argument and returns the
    # n-th input argument. The proper SSA way to do this would be phi-nodes.

    a = Operation("getarg", [Constant(0)])
    b = Operation("getarg", [Constant(1)])
    # var1 = add(b, 17)
    var1 = Operation("add", [b, Constant(17)])
    # var2 = mul(a, var1)
    var2 = Operation("mul", [a, var1])
    # var3 = add(b, 17)
    var3 = Operation("add", [b, Constant(17)])
    # var4 = add(var2, var3)
    var4 = Operation("add", [var2, var3])

    sequence = [a, b, var1, var2, var3, var4]
    # nothing to test really, it shouldn't crash


# Usually, complicated programs are represented as a control flow graph in a
# compiler, which represents all the possible paths that control can take while
# executing the program. Every node in the control flow graph is a basic block.
# A basic block is a linear sequence of operations with no control flow inside
# of it.

# https://en.wikipedia.org/wiki/Basic_block

# When optimizing a program, a compiler usually looks at the whole control flow
# graph of a function. However, that is still too complicated! So let's
# simplify further and look at only at optimizations we can do when looking at
# a single basic block and its sequence of instructions (they are called local
# optimizations).

# But let's define a class representing basic blocks first and let's also add
# some convenience functions for constructing sequences of operations, because
# the code in test_construct_example is a bit annoying.

class Block(list):
    def __getattr__(self, opname):
        # this looks a bit complicated! You can ignore the implementation and
        # just look at the test below to see an example of how to use it.
        # the main idea is that we cann just call any operation name on the
        # Block as a method and pass arguments to it and it will get
        # automatically get added to the basic block
        def wraparg(arg):
            if not isinstance(arg, Value):
                arg = Constant(arg)
            return arg
        def make_op(*args):
            # construct an Operation, wrap the arguments in Constants if
            # necessary
            op = Operation(opname, [wraparg(arg) for arg in args])
            # add it to self, the basic block
            self.append(op)
            return op
        return make_op

def test_convencience_block_construction():
    bb = Block()
    # a and b again with getarg
    a = bb.getarg(0)
    assert len(bb) == 1
    assert bb[0].name == "getarg"
    assert bb[0].args[0].value == 0 # it's a Constant

    b = bb.getarg(1)
    # var1 = add(b, 17)
    var1 = bb.add(b, 17)
    # var2 = mul(a, var1)
    var2 = bb.mul(a, var1)
    # var3 = add(b, 17)
    var3 = bb.add(b, 17)
    # var4 = add(var2, var3)
    var4 = bb.add(var2, var3)
    assert len(bb) == 6

# That's a good bit of infrastructure to make the tests easy to write. One
# thing we are lacking though is a way to print the basic blocks into a nicely
# readable textual representation. Because in the current form, the repr of a
# Block is very annoying, the output of pprint-ing bb in test above looks like
# this:

[Operation(name='getarg', args=[Constant(value=0)]),
 Operation(name='getarg', args=[Constant(value=1)]),
 Operation(name='add',
           args=[Operation(name='getarg', args=[Constant(value=1)]),
                 Constant(value=17)]),
 Operation(name='mul',
           args=[Operation(name='getarg', args=[Constant(value=0)]),
                 Operation(name='add',
                           args=[Operation(name='getarg',
                                           args=[Constant(value=1)]),
                                 Constant(value=17)])]),
 Operation(name='add',
           args=[Operation(name='getarg', args=[Constant(value=1)]),
                 Constant(value=17)]),
 Operation(name='add',
           args=[Operation(name='mul',
                           args=[Operation(name='getarg',
                                           args=[Constant(value=0)]),
                                 Operation(name='add',
                                           args=[Operation(name='getarg',
                                                           args=[Constant(value=1)]),
                                                 Constant(value=17)])]),
                 Operation(name='add',
                           args=[Operation(name='getarg',
                                           args=[Constant(value=1)]),
                                 Constant(value=17)])])]

# It's basically impossible to see what is going on here, because the
# Operations in the basic block appear several times, once as elements of the
# list but then also as arguments to operations further down in the list. so
# let's write some code that turns things back into a readable textual
# representation, so we have a chance to debug.

def basicblock_to_str(l : Block, varprefix : str = "var", extra_info=None):
    # the implementation is not too important, look at the test below to see
    # what the result looks like

    def arg_to_str(arg : Value):
        if isinstance(arg, Constant):
            return str(arg.value)
        else:
            # the key must exist, otherwise it's not a valid SSA basic block:
            # the variable must be defined before use
            return varnames[arg]

    varnames = {}
    res = []
    for index, op in enumerate(l):
        # give the operation a name used while printing:
        varname = varnames[op] = f"{varprefix}{index}"
        arguments = ", ".join(arg_to_str(op.arg(i)) for i in range(len(op.args)))
        strop = f"{varname} = {op.name}({arguments})"

        # ignore this mechanism for now, used much later. for now, extra_info
        # is always None
        if extra_info is not None and (extra := extra_info(op)) is not None:
            strop += f" # {extra}"
        res.append(strop)
    return "\n".join(res)

def test_basicblock_to_str():
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, var0)

    assert basicblock_to_str(bb) == """\
var0 = getarg(0)
var1 = add(5, 4)
var2 = add(var1, var0)"""

    # with a different prefix for the invented variable names:
    assert basicblock_to_str(bb, "x") == """\
x0 = getarg(0)
x1 = add(5, 4)
x2 = add(x1, x0)"""

    # and our running example:
    bb = Block()
    a = bb.getarg(0)
    b = bb.getarg(1)
    var1 = bb.add(b, 17)
    var2 = bb.mul(a, var1)
    var3 = bb.add(b, 17)
    var4 = bb.add(var2, var3)

    assert basicblock_to_str(bb, "v") == """\
v0 = getarg(0)
v1 = getarg(1)
v2 = add(v1, 17)
v3 = mul(v0, v2)
v4 = add(v1, 17)
v5 = add(v3, v4)"""
    # Note the re-numbering of the variables! We don't attach names to
    # Operations at all, so the printing will just number them in sequence, can
    # be sometimes a source of confusion.
    

# This is much better. Now we're done with the basic infrastructure, we can
# define sequences of operations. Next we need a central data structure that is
# used when actually optimizing basic blocks.

# Section 2 Union Find

# When optimizing a sequence of operations, we want to make it less costly to
# execute. For that we typically want to remove operations (and sometimes
# replace operations with less expensive ones). We can remove operations if
# they do redundant computation, like case of the duplicate `add(v1, 17)` in
# the example. So what we want to do is to turn the running input sequence:

# v0 = getarg(0)
# v1 = getarg(1)
# v2 = add(v1, 17)
# v3 = mul(v0, v2)
# v4 = add(v1, 17)
# v5 = add(v3, v4)


# into the following optimized output sequence:

# optvar0 = getarg(0)
# optvar1 = getarg(1)
# optvar2 = add(optvar1, 17)
# optvar3 = mul(optvar0, optvar2)
# optvar4 = add(optvar3, optvar2)

# We left out the second add (which defines v4), and then replaced the usage of
# v4 with v2 in the final operation.

# What we effectively did was discover that v2 and v4 are equivalent and then
# replaced v4 with v2. In general, we might discover more such equivalences,
# and we need a data structure to store them. A good data structure to store
# these equivalences is Union Find (also called Disjoint-set data structure),
# which stores a collection of disjoint sets. The sets in our concrete case are
# the sets of operations that compute the same result.

# When we start out, every operation is in its own singleton set, with no other
# member. As we discover more equivalences, we will unify sets into larger sets
# of operations that all compute the same result. So one operation the data
# structure supports is "union", to unify two sets.

# The other operation the data structure supports is "find", which takes an
# operation and returns a "representative" of the set of all equivalent
# operations. Two operations are in the same set, if the representative that
# find returns for them is the same.

# The exact details of how the data structure works are only sort of important,
# again it's ok to skip over the implementation. We will add the datastructure
# right into our Value, Constant and Operation classes:



# https://en.wikipedia.org/wiki/Disjoint-set_data_structure

class Value:
    def find(self):
        raise NotImplementedError("abstract base class")

@dataclass(eq=False)
class Operation(Value):
    name : str
    args : list

    forwarded : Optional[Value] = None

    def find(self) -> Value:
        # returns the "representative" value of self, in the union-find sense
        op = self
        while isinstance(op, Operation):
            # could do path compression here too but not essential
            next = op.forwarded
            if next is None:
                return op
            op = next
        return op

    def arg(self, index):
        # change to above:
        # return the representative of argument 'index'
        return self.args[index].find()

    def make_equal_to(self, value : Value):
        # this is "union" in the union-find sense, but the direction is
        # important! the representative of the union of Operations must be
        # either a Constant or an operation that we know for sure is not
        # optimized away.
        self.find().forwarded = value


@dataclass(eq=False)
class Constant(Value):
    value : object

    def find(self):
        return self


def test_union_find():
    # construct three operation, and unify them step by step
    bb = Block()
    a1 = bb.dummy(1)
    a2 = bb.dummy(2)
    a3 = bb.dummy(3)

    # at the beginning, every op is its own representative, that means every
    # operation is in a singleton set
    assert a1.find() is a1
    assert a2.find() is a2
    assert a3.find() is a3

    # now we unify a2 and a1
    a2.make_equal_to(a1)
    assert a1.find() is a1 # they both return a1 as the representative
    assert a2.find() is a1
    assert a3.find() is a3 # a3 is still different

    # now they are all the same
    a3.make_equal_to(a2)
    assert a1.find() is a1
    assert a2.find() is a1
    assert a3.find() is a1

    # now they are still all the same, and we also learned that they are the
    # same as the constant 6
    c = Constant(6)
    a2.make_equal_to(c)
    assert a1.find() is c
    assert a2.find() is c
    assert a3.find() is c


# Section: Constant Folding

# Now comes the first actual optimization pass (at first I will show individual
# optimization passes, later they will be combined into a single pass).

# Every pass has the same structure: we go over all operations in the basic
# block in order and decide for each operation whether it can be removed.

# I will show a buggy version of the constant folding pass first. It has a
# problem that is related to why we need the union-find data structure. We will
# fix it a bit further down.

def constfold_buggy(bb: Block) -> Block:
    opt_bb = Block()

    for op in bb:
        # basic idea: go over the list and do constant folding of add where
        # possible
        if op.name == "add":
            arg0 = op.args[0]
            arg1 = op.args[1]
            if isinstance(arg0, Constant) and isinstance(arg1, Constant):
                # can constant-fold! that means we learned a new equality,
                # namely that op is equal to a specific constant
                op.make_equal_to(Constant(arg0.value + arg1.value))
                # don't need to have the operation in the optimized basic block
                continue
        # otherwise the operation is not constant-foldable and put into the
        # output list
        opt_bb.append(op)
    return opt_bb


def test_constfold_simple():
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, var0)

    opt_bb = constfold_buggy(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(9, optvar0)"""

@pytest.mark.xfail
def test_constfold_buggy_limitation():
    # this test fails! it shows the problem with the above simple
    # constfold_buggy pass

    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(5, 4) # this is folded
    var2 = bb.add(var1, 10) # we want this folded too, but it doesn't work
    var3 = bb.add(var2, var0)

    opt_bb = constfold_buggy(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""

# why does the test fail? The opt_bb printed output looks like this:
# optvar0 = getarg(0)
# optvar1 = add(9, 10)
# optvar2 = add(optvar1, optvar0)

# The problem is that when we optimize the second addition in
# constfold_buggy, the argument of that operation is an *Operation* not a
# Constant, so constant-folding is not applied to the second add. However,
# we have already learned that the argument var1 to the operation var2 is
# equal to Constant(9). This information is stored in the union-find data
# structure. So what we are missing are suitable find calls in
# the constant folding pass, to make use of the previously learned
# equalities


# here's the fixed version:

def constfold(bb: Block) -> Block:
    opt_bb = Block()

    for op in bb:
        # basic idea: go over the list and do constant folding of add where
        # possible
        if op.name == "add":
            # >>> changed
            arg0 = op.arg(0) # uses .find()
            arg1 = op.arg(1) # uses .find()
            # <<< end changes
            if isinstance(arg0, Constant) and isinstance(arg1, Constant):
                # can constant-fold! that means we learned a new equality,
                # namely that op is equal to a specific constant
                op.make_equal_to(Constant(arg0.value + arg1.value))
                continue # don't need to have the optimization in the result
        # otherwise the operation is put into the output list
        opt_bb.append(op)
    return opt_bb


def test_constfold_two_ops():
    # now it works!
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, 10)
    var3 = bb.add(var2, var0)
    opt_bb = constfold(bb)

    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""


# _____________________________________________________________________

# The constfold pass only discovers equalities between Operations and
# Constants. Let's do a second pass that also discovers equalities between
# Operations and other Operations.

# A simple optimization that does that is common subexpression elimination
# (CSE).


def cse(bb : Block) -> Block:
    # structure is the same, loop over the input, add some but not all
    # operations to the output

    opt_bb = Block()

    for op in bb:
        # only do CSE for add here, but it generalizes
        if op.name == "add":
            arg0 = op.args[0].find()
            arg1 = op.args[1].find()
            # Check whether we have emitted the same operation already
            prev_op = find_prev_add_op(arg0, arg1, opt_bb)
            if prev_op is not None:
                # if yes, we can optimize op away and replace it with the
                # earlier result, which is an Operation that was already
                # emitted to opt_bb
                op.make_equal_to(prev_op)
                continue
        opt_bb.append(op)
    return opt_bb


def eq_value(val0, val1):
    if isinstance(val0, Constant) and isinstance(val1, Constant):
        # constants compare by their value
        return val0.value == val1.value
    # everything else by identity
    return val0 is val1


def find_prev_add_op(arg0 : Value, arg1 : Value, opt_bb : Block) -> Optional[Operation]:
    # Really naive and quadratic implementation. what we do is walk over the
    # already emitted operations and see whether we emitted an add with the
    # current arguments already. A real implementation might use a hashmap of
    # some kind, or at least only look at a limited window of instructions.
    for opt_op in opt_bb:
        if opt_op.name != "add":
            continue
        # It's important to call find here, for the same reason why we needed
        # it in constfold.
        if eq_value(arg0, opt_op.args[0].find()) and eq_value(arg1, opt_op.args[1].find()):
            return opt_op
    return None


def test_cse():
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.getarg(1)
    var2 = bb.add(var0, var1)
    var3 = bb.add(var0, var1) # the same as var3
    var4 = bb.add(var2, 2)
    var5 = bb.add(var3, 2) # the same as var4
    var6 = bb.add(var4, var5)

    opt_bb = cse(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = add(optvar0, optvar1)
optvar3 = add(optvar2, 2)
optvar4 = add(optvar3, optvar3)"""


# _____________________________________________________________________

# now we have a pass that replaces Operations with Constants and one that
# replaces Operations with previously existing Operations. Let's now do one
# final pass that replaces Operations by newly invented Operations, a simple
# strength reduction

def strength_reduce(bb: Block) -> Block:
    opt_bb = Block()
    for op in bb:
        if op.name == "add":
            arg0 = op.args[0].find()
            arg1 = op.args[1].find()
            if arg0 is arg1: # x + x turns into x << 1
                newop = opt_bb.lshift(arg0, 1)
                op.make_equal_to(newop)
                continue
        opt_bb.append(op)
    return opt_bb

def test_strength_reduce():
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(var0, var0)

    opt_bb = strength_reduce(bb)

    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""

# _____________________________________________________________________

# Let's combine the passes into one single pass, so that we are going over all
# the operations only exactly once.

def optimize_prelim(bb: Block) -> Block:
    opt_bb = Block()

    for op in bb:
        if op.name == "add":
            arg0 = op.args[0].find()
            arg1 = op.args[1].find()

            # constant folding
            if isinstance(arg0, Constant) and isinstance(arg1, Constant):
                op.make_equal_to(Constant(arg0.value + arg1.value))
                continue

            # cse
            prev_op = find_prev_add_op(arg0, arg1, opt_bb)
            if prev_op is not None:
                op.make_equal_to(prev_op)
                continue

            # strength reduce
            if arg0 is arg1: # x + x turns into x << 1
                newop = opt_bb.lshift(arg0, 1)
                op.make_equal_to(newop)
                continue

            # and while we are at it, let's do some arithmetic simplification:
            # a + 0 => a
            if eq_value(arg0, Constant(0)):
                op.make_equal_to(arg1)
                continue
            if eq_value(arg1, Constant(0)):
                op.make_equal_to(arg0)
                continue
        opt_bb.append(op)
    return opt_bb


# some tests for the preliminary combined optimizer:

def test_single_pass_prelim():
    bb = Block()
    # constant folding
    var0 = bb.getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, 10)
    var3 = bb.add(var2, var0)

    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""

    # cse + strength reduction
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.getarg(1)
    var2 = bb.add(var0, var1)
    var3 = bb.add(var0, var1) # the same as var3
    var4 = bb.add(var2, 2)
    var5 = bb.add(var3, 2) # the same as var4
    var6 = bb.add(var4, var5)

    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = add(optvar0, optvar1)
optvar3 = add(optvar2, 2)
optvar4 = lshift(optvar3, 1)"""

    # removing + 0
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.add(16, -16)
    var2 = bb.add(var0, var1)
    var3 = bb.add(0, var2)
    var4 = bb.add(var2, var3)

    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""


# That's it for now. Why is this architecture cool? From a software engineering
# point of view, sticking everything into a single function like in
# optimize_xxxxxxxxxxxxxxxxxxxxxxx above is obviously not great, and if you wanted to do this
# for real you would try to split the cases into different functions that are
# individually digestible, or even use a DSL that makes the pattern matching
# much more readable. But the advantage of the architecture is that it's quite
# efficient, it makes it possible to pack a lot of good optimizations into a
# single pass over a basic block.

# Of course this works even better if you are in a tracing context, where
# everything is put into a trace, which is basically one incredibly long basic
# block. And indeed this is exactly the architecture that PyPy's JIT optimizer
# uses. In a JIT context it's also quite important that the optimizer itself
# runs quickly.

# Various other optimizations are possible in this model. I plan to write a
# follow-up post that shows PyPy's most important optimization.

