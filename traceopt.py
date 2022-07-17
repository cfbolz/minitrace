import pytest
import re
from dataclasses import dataclass

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
# computed twice and we can save time by calling it only once. In this post I
# want to show an optimizer that can do this (and some related) optimizations.

# I will not at all talk about the process of translating the input program
# into the IR. Instead, I will assume we have some component that does this
# translation already. The tests in this blog post will construct small
# snippets of IR by hand.

# Looking at the IR we notice that the input expression has been linearized
# into a sequence of operations, and all the intermedia results have been given
# unique variable names. The value that every variable is assigned is computed
# by some operation, which consist of an operand and an arbitrary number of
# arguments. The arguments of an operation are either themselves variables or
# constants.

# Section 1 the IR

# Let's start modelling some of this with Python classes. First we define a
# base class of all values that can be used as arguments in operations, and
# let's also add a class that represents constants:

# https://en.wikipedia.org/wiki/Control-flow_graph

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

    def getarg(self, index):
        return self.args[index]

# Now we can instantiate these two classes to represent the example sequence of
# operations above:

def test_construct_example():
    # first we need something to represent "b". In our limited view, we don't
    # know where it comes from, so we will define it with a pseudo-operation
    # called "getarg" which takes a number n as an argument and returns the
    # n-th input argument

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
# a single basic block and its sequence of instructions.

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
    import pprint
    pprint.pprint(list(bb))
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

# It's basically impossible to see what is going on here, because there the
# Operations in the basic block appear several times, once as elements of the
# list but then also as arguments to operations further down in the list. so
# let's write some code that turns things back into a readable textual
# representation, so we have a chance to debug.

def basicblock_to_str(l : list[Operation], varprefix : str = "var", extra_info=None):
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
    for op in l:
        # give the operation a name used while printing:
        varname = varnames[op] = f"{varprefix}{len(varnames)}"
        arguments = ", ".join(arg_to_str(op.getarg(i)) for i in range(op.numargs))
        strop = f"{varname} = {op.name}({arguments})"

        # ignore this mechanism for now, used much later. for now, extra_info
        # is always None
        if extra_info is not None and (extra := extra_info(op)) is not None:
            strop += f" # {extra}"
        res.append(strop)
    return "\n".join(res)

def test_basicblock_to_str():
    # the basic block would usually start with phi nodes, I am not
    # modelling that in this small sketch. let's use a pseudo-operation
    # 'getarg' for variables that flow into the block

    bb = Block()
    var0 = getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, var0)

    bb = [var0, var1, var2]
    assert basicblock_to_str(bb) == """\
var0 = getarg(0)
var1 = add(5, 4)
var2 = add(var1, var0)"""

    assert basicblock_to_str(bb, "x") == """\
x0 = getarg(0)
x1 = add(5, 4)
x2 = add(x1, x0)"""

# the idea of this file is to show how a union-find data structure can be used
# in an extremely simple local forward optimization pass. that pass will go
# over the operations of a single basic block once in the forward direction and
# returns a new (shorter) list of optimized operations

# the approach is somewhat limited in that it is "local", ie only works for
# basic blocks. It can be extended to work for extended basic blocks (making it
# a superlocal optimizations).

# the union find datastructure sorts the input operations in the basic blocks
# into equivalence classes of operations that must all compute the same result.
# As the various optimizations discover equalities, they call union. Every one
# of these equivalence classes gets a representative, which is either an
# operation that has to be emitted into the optimized basic block, or sometimes
# even a constant.

# let's start with the IR:

# the following classes represent the operations in our mini IR: Operations
# (which are the same thing as variables in the SSA sense) and Constants

class Value:
    def find(self):
        raise NotImplementedError("abstract base class")

@dataclass(eq=False)
class Operation(Value):
    name : str
    args : list
    forwarded : Value = None

    info = None

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

def parse(lines):
    bb = []
    names = {}
    for line in lines.splitlines():
        line = line.strip()
        if not line:
            continue
        varname = None
        if "=" in line:
            varname, line = line.split("=", 1)
            varname = varname.strip()
        paren_pos = line.find('(')
        assert paren_pos >= 1
        opname = line[:paren_pos].strip()
        assert line[-1] == ')'
        line = line[paren_pos + 1:-1] # cut of parens
        opargs = []
        for arg in line.split(','):
            arg = arg.strip()
            if arg in names:
                oparg = names[arg]
            else:
                oparg = Constant(int(arg))
            opargs.append(oparg)
        op = Operation(opname, opargs, varname)
        bb.append(op)
        if varname:
            assert varname not in names
            names[varname] = op
    return bb

def eq_basic_block(bb1, bb2):
    return basicblock_to_str(bb1) == basicblock_to_str(bb2)

def test_parse():
    s = """\
var0 = getarg(0)
var1 = add(5, 4)
var2 = add(var1, var0)"""
    bb = parse(s)
    assert basicblock_to_str(bb) == s


# helper function for construction Operation instances that wrap the arguments
# into Constant if they aren't Values already, to make writing the examples
# more convenient

def opbuilder(opname):
    def wraparg(arg):
        if not isinstance(arg, Value):
            arg = Constant(arg)
        return arg
    def build(*args):
        return Operation(opname, [wraparg(arg) for arg in args])
    return build

add = opbuilder("add")
getarg = opbuilder("getarg")
dummy = opbuilder("dummy")
lshift = opbuilder("lshift")

# these above definitions allow us to write
# add(1, 2)
# instead of Operation("add", [Constant(1), Constant(2)])


def test_union_find():
    # construct three operation, and unify them step by step
    bb = Block()
    a1 = bb.dummy(1)
    a2 = bb.dummy(2)
    a3 = bb.dummy(3)
    assert a1.find() is a1
    assert a2.find() is a2
    assert a3.find() is a3

    a2.make_equal_to(a1)
    assert a1.find() is a1
    assert a2.find() is a1
    assert a3.find() is a3

    a3.make_equal_to(a2)
    assert a1.find() is a1
    assert a2.find() is a1
    assert a3.find() is a1

    c = Constant(6)
    a2.make_equal_to(c)
    assert a1.find() is c
    assert a2.find() is c
    assert a3.find() is c


# that's the implementation of the IR and the methods needed for union find.
# let's look at how to optimize basic blocks (=lists of Operations)


# _____________________________________________________________________

# a basic block is a list of Operations. first, a convenience function to print
# basic blocks:

def basicblock_to_str(l : list[Operation], varprefix : str = "var", extra_info=None):
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
    for op in l:
        # give the operation a name used while printing:
        varname = varnames[op] = f"{varprefix}{len(varnames)}"
        arguments = ", ".join(arg_to_str(arg.find()) for arg in op.args)
        strop = f"{varname} = {op.name}({arguments})"

        # ignore this mechanism for now, used much later. for now, extra_info
        # is always None
        if extra_info is not None and (extra := extra_info(op)) is not None:
            strop += f" # {extra}"
        res.append(strop)
    return "\n".join(res)

def test_basicblock_to_str():
    # the basic block would usually start with phi nodes, I am not
    # modelling that in this small sketch. let's use a pseudo-operation
    # 'getarg' for variables that flow into the block

    bb = Block()
    var0 = getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, var0)

    bb = [var0, var1, var2]
    assert basicblock_to_str(bb) == """\
var0 = getarg(0)
var1 = add(5, 4)
var2 = add(var1, var0)"""

    assert basicblock_to_str(bb, "x") == """\
x0 = getarg(0)
x1 = add(5, 4)
x2 = add(x1, x0)"""

    # check that it interacts correctly with the union-find datastructure:
    # if we unify var1 with the Constant 9, then var1 should be printed as 9
    # when printing var2
    var1.make_equal_to(Constant(9))
    opt_bb = [var0, var2]

    # printing should see that replacement in the way it shows var2, due to the
    # find call in the implementation above:
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(9, optvar0)"""


# _____________________________________________________________________

# Now comes the first actual optimization pass. For now, let's split the
# optimizer into several passes, one for constant folding, one for common
# subexpression elimination, one for strength reduction. later we will combine
# them into a single pass

# Every pass has the same structure: we go over all operations in the basic
# block in order and decide for each operation it can be removed.

# First we'll look at a simple constant folding pass. I will show a buggy
# version of that pass first. It has a problem that is related to why we need
# the union-find data structure. We will fix it a bit further down.

def constfold_buggy(bb: list[Operation]) -> list[Operation]:
    opt_bb = []

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
    # reuse the simple example from the last test, this time do the
    # optimization for real
    bb = Block()
    var0 = getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, var0)

    bb = [var0, var1, var2]
    opt_bb = constfold_buggy(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(9, optvar0)"""

@pytest.mark.xfail
def test_constfold_buggy_limitation():
    # this test fails! it shows the problem with the above simple
    # constfold_buggy pass

    bb = Block()
    var0 = getarg(0)
    var1 = bb.add(5, 4) # this is folded
    var2 = bb.add(var1, 10) # we want this folded too, but it doesn't work
    var3 = bb.add(var2, var0)

    bb = [var0, var1, var2, var3]
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

def constfold(bb: list[Operation]) -> list[Operation]:
    opt_bb = []

    for op in bb:
        # basic idea: go over the list and do constant folding of add where
        # possible
        if op.name == "add":
            arg0 = op.args[0].find() # <====== changed
            arg1 = op.args[1].find() # <====== changed
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
    var0 = getarg(0)
    var1 = bb.add(5, 4)
    var2 = bb.add(var1, 10)
    var3 = bb.add(var2, var0)

    bb = [var0, var1, var2, var3]
    opt_bb = constfold(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""


# _____________________________________________________________________

# the constfold pass only discovers equalities between Operations and
# Constants. let's do a second pass that also discovers equalities between
# Operations and other Operations.

# a simple optimization that does that is common subexpression elimination
# (CSE)


def cse(bb : list[Operation]) -> list[Operation]:
    # structure is the same, loop over the input, add some but not all
    # operations to the output

    opt_bb = []

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


def find_prev_add_op(arg0 : Value, arg1 : Value, opt_bb : list[Operation]) -> Operation | None:
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

def strength_reduce(bb: list[Operation]) -> list[Operation]:
    opt_bb = []
    for op in bb:
        if op.name == "add":
            arg0 = op.args[0].find()
            arg1 = op.args[1].find()
            if arg0 is arg1: # x + x turns into x << 1
                newop = lshift(arg0, 1)
                opt_bb.append(newop)
                op.make_equal_to(newop)
                continue
        opt_bb.append(op)
    return opt_bb

def test_strength_reduce():
    bb = Block()
    var0 = getarg(0)
    var1 = add(var0, var0)

    opt_bb = strength_reduce([var0, var1])

    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""

# _____________________________________________________________________

# Let's combine the passes into one single pass, so that we are going over all
# the operations only exactly once.

def optimize_prelim(bb: list[Operation]) -> list[Operation]:
    opt_bb = []

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
                newop = lshift(arg0, 1)
                opt_bb.append(newop)
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
    var0 = getarg(0)
    var1 = add(5, 4)
    var2 = add(var1, 10)
    var3 = add(var2, var0)

    bb = [var0, var1, var2, var3]
    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""

    # cse + strength reduction
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = add(var0, var1)
    var3 = add(var0, var1) # the same as var3
    var4 = add(var2, 2)
    var5 = add(var3, 2) # the same as var4
    var6 = add(var4, var5)

    bb = [var0, var1, var2, var3, var4, var5, var6]
    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = add(optvar0, optvar1)
optvar3 = add(optvar2, 2)
optvar4 = lshift(optvar3, 1)"""

    # removing + 0
    bb = Block()
    var0 = getarg(0)
    var1 = add(16, -16)
    var2 = add(var0, var1)
    var3 = add(0, var2)
    var4 = add(var2, var3)

    bb = [var0, var1, var2, var3, var4]
    opt_bb = optimize_prelim(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""


# _____________________________________________________________________
#
# Attaching additional information to Operations

# Now there is one more fundamental feature we can add to this way of writing
# one-pass optimizers. We want to do a bit of analysis while we go along the
# list of operations that we optimize. The information such an analysis learns
# should be attached to each equivalence class of operations. The analysis
# results can then be used to optimize some operations in better ways.

# A typical example of such an analysis would for example be an integer range
# analysis, where the optimizer tries to figure out whether the result of an
# operation must be in a specific range. This analysis is a bit too complex to
# write it down here, so we will do a much simpler one. The analysis will keep
# track of whether the result of operation is known to be even, known to be
# odd, or its parity is unknown. That is not really an incredibly useful piece
# of knowledge to have for an optimizer, but it does help in some situations
# and it's relatively easy to describe.

# We can store parity knowledge in the following class:

PARITY_EVEN = "even"
PARITY_ODD = "odd"
PARITY_UNKNOWN = "unknown"

# (we could use an enum here too, but this is good enough).

@dataclass
class IntegerInfo:
    parity : str


# We could like to attach an instance of IntegerInfo to an equivalence class of
# Operations. To do that, we attach it to a new field "info" of the Operation
# instance. We can retrieve the IntegerInfo for a value like this:

def get_integer_info(value : Value):
    value = value.find()
    if isinstance(value, Constant):
        # we can compute the parity of Constants, it is always known:
        if value.value & 1:
            parity = PARITY_ODD
        else:
            parity = PARITY_EVEN
        return IntegerInfo(parity)
    else:
        assert isinstance(value, Operation)
        info = value.info

        # if we don't have an instance of IntegerInfo yet, we don't know anything
        # about the parity, so the parity is unknown
        if info is None:
            info = value.info = IntegerInfo(PARITY_UNKNOWN)

        # otherwise return the existing info
        return info

def test_integer_info():
    assert get_integer_info(Constant(12)).parity == PARITY_EVEN
    assert get_integer_info(Constant(-17)).parity == PARITY_ODD
    assert get_integer_info(dummy(12)).parity == PARITY_UNKNOWN


# how does the optimizer actually learn anything about the parity of results of
# operations? Of the operations we have used so far, only lshift tells us
# anything about parity, the result is always even if the second argument is
# larger than 0. For additions, if the arguments have known parity, we can
# compute the parity of the result. So let's write a small analysis that tries
# to compute the parity of as many operations as possible, again in a single
# pass:


def analyze_parity(bb : list[Operation]) -> None:
    # the analysis does not actually return anything, instead, it has the side
    # effect of attaching IntegerInfo objects to some Operations in bb

    # the analysis works as a forward pass again
    for op in bb:
        if op.name == "lshift":
            if isinstance(op.args[1], Constant) and op.args[1].value > 0:
                info = get_integer_info(op)
                info.parity = PARITY_EVEN
        elif op.name == "add":
            # get the information about both arguments, and if they both are
            # known, we can compute the parity of the result
            info0 = get_integer_info(op.args[0])
            info1 = get_integer_info(op.args[1])
            if info0.parity != PARITY_UNKNOWN and info1.parity != PARITY_UNKNOWN:
                info = get_integer_info(op)
                if info0.parity == info1.parity:
                    info.parity = PARITY_EVEN
                else:
                    info.parity = PARITY_ODD


def print_extra_info_parity(op):
    info = get_integer_info(op)
    if info.parity != PARITY_UNKNOWN:
        return info.parity

def test_analyze_parity():
    # let's try this on some operations!
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = lshift(var0, 1) # known even
    var3 = add(var2, 5) # known odd
    var4 = add(var2, 16) # known even
    var5 = add(var4, var1) # unknown, because var1 has unknown parity
    bb = [var0, var1, var2, var3, var4, var5]
    analyze_parity(bb)

    # we can use the extra_info argument of the basicblock_to_str function to
    # print the computed parities as comments:
    assert basicblock_to_str(bb, extra_info=print_extra_info_parity) == """\
var0 = getarg(0)
var1 = getarg(1)
var2 = lshift(var0, 1) # even
var3 = add(var2, 5) # odd
var4 = add(var2, 16) # even
var5 = add(var4, var1)"""

# Cool, so the analysis works, we managed to learn something about the values
# in our programs in some situations. We don't just want to learn something for
# the sake of it though, we can to use the information for optimizing the
# program. Now this is going to be a little bit contrived, but in order to be
# able to optimize something, we need a new bitwise_and operation:

bitwise_and = opbuilder("bitwise_and")

# If we encounter an operation bitwise_and(x, 1) we can compute the result of
# that if we know the parity of x. Let's write a small pass that does only
# that:

def optimize_with_parity(bb : list[Operation]) -> list[Operation]:
    # the general structure is the same as all the other small optimization
    # passes we've written before, however, this time we call analyze first.
    analyze_parity(bb)

    opt_bb = []
    for op in bb:
        if op.name == "bitwise_and":
            arg0 = op.args[0].find()
            info = get_integer_info(arg0)
            arg1 = op.args[1].find()
            if info.parity != PARITY_UNKNOWN and isinstance(arg1, Constant) and arg1.value == 1:
                # we know the parity of arg0 and arg1 is the constant 1, remove the op
                if info.parity == PARITY_EVEN:
                    result = 0
                else:
                    result = 1
                op.make_equal_to(Constant(result))
                continue
        opt_bb.append(op)
    return opt_bb


def test_optimize_with_parity():
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = lshift(var0, 1) # known even
    var3 = add(var2, 5) # known odd
    var4 = add(var2, 16) # known even
    var5 = bitwise_and(var2, 1) # 0
    var6 = bitwise_and(var3, 1) # 1
    var7 = bitwise_and(var4, 1) # 0
    var8 = add(var5, var6)
    var9 = add(var8, var7)
    var10 = add(var1, var9)

    bb = [var0, var1, var2, var3, var4, var5, var6, var7, var8, var9, var10]
    # first do parity optimization, then a bit of constant folding etc
    opt_bb = optimize_prelim(optimize_with_parity(bb))

    assert basicblock_to_str(opt_bb, "optvar", print_extra_info_parity) == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = lshift(optvar0, 1) # even
optvar3 = add(optvar2, 5) # odd
optvar4 = add(optvar2, 16) # even
optvar5 = add(optvar1, 1)"""

# Cool! Arguably a contrived example, but all the bitwise_ands were removed. We
# later want to put the parity optimizations into the same pass as all the
# other optimizations, but let's focus first on another problem that this
# example shows.

# The problem is that after removing the bitwise_ands, optvar2, optvar3 and
# optvar4 are unused and should just be removed (let's assume that optvar5 gets
# passed to the next basic block). The only use of these now unused variables
# was as arguments to the bitwise_ands, and those are removed from the program.
# Unfortunately, there is one thing that a single forward pass is fundamentally
# unable to compute, which is lifeness. Therefore to achieve dead code
# elimination (DCE), we need a single backwards pass too:

def dce(bb : list[Operation], results : set[Operation]):
    # the second argument to dce is for passing "result" variables, those that
    # must remain alive at the end of the block, for example because they get
    # passed on to further blocks. if you pass the empty set there *everything*
    # gets removed.

    opt_bb = []
    alive = results

    # this code assumes that all operations have no side effects and can be
    # removed if their result isn't needed. it would be easy to extend the dce
    # pass to support operations that have side effects

    for op in reversed(bb):
        if op not in alive:
            # op has not been seen as an argument to any operation further down
            # in the list of operations. Therefore it is dead and can be left
            # out.
            continue
        for arg in op.args:
            # op is alive! therefore all of its arguments need to be alive too
            if isinstance(arg, Constant):
                continue
            alive.add(arg)
        opt_bb.append(op)
    return list(reversed(opt_bb))

def test_dead_code_elimination():
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = lshift(var0, 1)
    var3 = add(var2, 5)
    var4 = add(var2, 16)
    var5 = add(var1, 1)
    bb = [var0, var1, var2, var3, var4, var5]

    opt_bb = dce(bb, {var5})
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(1)
optvar1 = add(optvar0, 1)"""


# so that's getting rid of the dead operations. The final thing I want to do is
# combine parity analysis and parity optimization with optimize_prelim into our
# final optimizer:


def optimize_forward(bb: list[Operation]) -> list[Operation]:
    opt_bb = []

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
            if arg0 is arg1: # x + x turns into x << 1, the result is even
                newop = lshift(arg0, 1)
                newop.info = IntegerInfo(PARITY_EVEN)
                opt_bb.append(newop)
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

            # the couldn't simplify the add operation, let's try to see whether
            # we can know something about it's parity:
            info0 = get_integer_info(op.args[0])
            info1 = get_integer_info(op.args[1])
            if info0.parity != PARITY_UNKNOWN and info1.parity != PARITY_UNKNOWN:
                info = get_integer_info(op)
                if info0.parity == info1.parity:
                    info.parity = PARITY_EVEN
                else:
                    info.parity = PARITY_ODD
            # done with add!

        elif op.name == "lshift":
            if isinstance(op.args[1], Constant):
                arg1value = op.args[1].value
                if arg1value == 0:
                    # x << 0 => x
                    op.make_equal_to(op.args[0].find())
                    continue
                # otherwise, we at least know the result is even
                info = get_integer_info(op)
                info.parity = PARITY_EVEN

        elif op.name == "bitwise_and":
            arg0 = op.args[0].find()
            info = get_integer_info(arg0)
            arg1 = op.args[1].find()
            if info.parity != PARITY_UNKNOWN and isinstance(arg1, Constant) and arg1.value == 1:
                # we know the parity of arg0 and arg1 is the constant 1, remove the op
                if info.parity == PARITY_EVEN:
                    result = 0
                else:
                    result = 1
                op.make_equal_to(Constant(result))
                continue

            # a possible improvement here: we could propagate the parity of
            # bitwise_and

        opt_bb.append(op)
    return opt_bb

def optimize(bb : list[Operation], results : set[Operation]):
    # combine the forward and the backward pass into one function
    opt_bb = optimize_forward(bb)

    # need to ask for the current representation of the equivalence class for
    # all results
    results = {result.find() for result in results}
    return dce(opt_bb, results)


def test_single_pass_final():
    # basically all the examples that have been working so far, plus parity
    # optimizations. since there is also DCE, we need to say which results we
    # want to keep

    # constant folding
    bb = Block()
    var0 = getarg(0)
    var1 = add(5, 4)
    var2 = add(var1, 10)
    var3 = add(var2, var0)

    bb = [var0, var1, var2, var3]
    opt_bb = optimize(bb, {var3})
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""

    # cse + strength reduction
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = add(var0, var1)
    var3 = add(var0, var1) # the same as var3
    var4 = add(var2, 2)
    var5 = add(var3, 2) # the same as var4
    var6 = add(var4, var5)

    bb = [var0, var1, var2, var3, var4, var5, var6]
    opt_bb = optimize(bb, {var6})
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = add(optvar0, optvar1)
optvar3 = add(optvar2, 2)
optvar4 = lshift(optvar3, 1)"""

    # removing + 0
    bb = Block()
    var0 = getarg(0)
    var1 = add(16, -16)
    var2 = add(var0, var1)
    var3 = add(0, var2)
    var4 = add(var2, var3)

    bb = [var0, var1, var2, var3, var4]
    opt_bb = optimize(bb, {var4})
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""

    # parity optimizations
    bb = Block()
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = lshift(var0, 1) # known even
    var3 = add(var2, 5) # known odd
    var4 = add(var2, 16) # known even
    var5 = bitwise_and(var2, 1) # 0
    var6 = bitwise_and(var3, 1) # 1
    var7 = bitwise_and(var4, 1) # 0
    var8 = add(var5, var6)
    var9 = add(var8, var7)
    var10 = add(var1, var9)

    bb = [var0, var1, var2, var3, var4, var5, var6, var7, var8, var9, var10]
    # first do parity optimization, then a bit of constant folding etc
    opt_bb = optimize(bb, {var10})

    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(1)
optvar1 = add(optvar0, 1)"""

# And we're done! Thanks for sticking with mean!

# Why is this architecture cool? From a software engineering point of view,
# sticking everything into a single function like in optimize_forward above is
# obviously not great, and if you wanted to do this for real you would try to
# split the cases into different functions that are individually digestible, or
# even use a DSL that makes the pattern matching much more readable.
# But the advantage of the architecture is that it's quite efficient, packing a
# lot of good optimizations into two passes over every basic block.

# Of course this works even better if you are in a tracing context, where
# everything is put into a trace, which is basically one incredibly long basic
# block. And indeed this is exactly the architecture that PyPy's JIT optimizer
# uses.

# I wanted to connect some of the concepts used in this sketch to theory and
# related work, here at the end. XXX ternary bits, abstract domains, partial
# evaluation, tracing JITs, LuaJIT

# framework can be applied to much more powerful optimizations, including
# allocation removal

# thanks (Per, Peng Wu, Max, Thorsten, Matti)
