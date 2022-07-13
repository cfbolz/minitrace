import pytest
from dataclasses import dataclass

# the idea of this file is to show how the union-find algorithm can be used in
# an extremely simple local forward optimization pass. that pass will go over
# the operations of a basic block once in the forward direction and returns a
# new (shorter) list of optimized operations

# the approach is somewhat limited in that it is "local", ie only works for
# basic blocks. It can be extended to work for extended basic blocks (making it
# a superlocal optimizations).


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
        # important! the representative of the union of operations must be
        # either a Constant or an operation that we know for sure is not
        # optimized away.
        self.find().forwarded = value

    def eq(self, other):
        return self == other # just by identity
      
@dataclass(eq=False)
class Constant(Value):
    value : object

    def find(self):
        return self

    def eq(self, other):
        return self.value == other.value
      
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
    a1 = dummy(1)
    a2 = dummy(2)
    a3 = dummy(3)
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

# a basic block is a list of Operations. first, aconvenience function to print
# basic blocks:

def basicblock_to_str(l : list[Operation], varprefix : str = "var"):
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
        res.append(f"{varname} = {op.name}({arguments})")
    return "\n".join(res)

def test_basicblock_to_str():
    # the basic block would usually start with phi nodes, I am not
    # modelling that in this small sketch. let's use a pseudo-operation
    # 'getarg' for variables that flow into the block

    var0 = getarg(0)
    var1 = add(5, 4)
    var2 = add(var1, var0)

    bb = [var0, var1, var2]
    assert basicblock_to_str(bb) == """\
var0 = getarg(0)
var1 = add(5, 4)
var2 = add(var1, var0)"""


    # check that it interacts correctly with the union-find datastructure:
    # let's say our still to-be-written optimizer did constant folding and
    # replaced var2 with 9, and removed the op from the bb:
    var1.make_equal_to(Constant(9))
    opt_bb = [var0, var2]

    # printing should see that replacement in the way it shows var2, due to the
    # find call:
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(9, optvar0)"""


# _____________________________________________________________________

# now comes the first actual optimization pass. for now, let's split the
# optimizer into several passes, one for constant folding, one for common
# subexpression elimination, one for strength reduction. later we will combine
# them into a single pass

# first a simple constant folding pass. I will show a buggy version of that
# pass first. It has a problem that is related to why we need the union-find
# data structure. We will fix it a bit further down.

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
                continue # don't need to have the operation in the result
        # otherwise the operation is put into the output list
        opt_bb.append(op)
    return opt_bb


def test_constfold_simple():
    # reuse the simple example from the last test, this time do the
    # optimization for real
    var0 = getarg(0)
    var1 = add(5, 4)
    var2 = add(var1, var0)

    bb = [var0, var1, var2]
    opt_bb = constfold_buggy(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(9, optvar0)"""

@pytest.mark.xfail
def test_constfold_buggy_limitation():
    # this test fails! it shows the problem with the above simple
    # constfold_buggy pass

    var0 = getarg(0)
    var1 = add(5, 4) # this is folded
    var2 = add(var1, 10) # we want this folded too! but it doesn't work
    var3 = add(var2, var0)

    bb = [var0, var1, var2, var3]
    opt_bb = constfold_buggy(bb)
    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(19, optvar0)"""

    #  the test fails! the opt_bb printed output looks like this:
    # optvar0 = getarg(0)
    # optvar1 = add(9, 10)
    # optvar2 = add(optvar1, optvar0)

    # why is that? the problem is that when we optimize the second addition in
    # constfold_buggy, the argument of that operation is an *Operation* not a
    # Constant, so constant-folding is not applied to the second add. However,
    # we have already learned that the argument var1 to the operation var2 is
    # equal to Constant(9). This information is stored in the union-find data
    # structure. So what we are missing are suitable find calls in
    # constfold_buggy


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
    var0 = getarg(0)
    var1 = add(5, 4)
    var2 = add(var1, 10)
    var3 = add(var2, var0)

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
            # really naive and quadratic implementation, a real one might use a
            # hash-map of some kind. what we do is walk over the already
            # emitted operations and see whether we emitted an add with the
            # current arguments already.
            prev_op = find_prev_add_op(op, opt_bb)
            if prev_op is not None:
                # optimize it away and replace it with the earlier result,
                # which is an Operation that was already emitted to opt_bb
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


def find_prev_add_op(op : Operation, opt_bb : list[Operation]) -> Operation | None:
    arg0 = op.args[0].find()
    arg1 = op.args[1].find()
    for opt_op in opt_bb:
        if opt_op.name != "add":
            continue
        if eq_value(opt_op.args[0].find(), arg0) and eq_value(opt_op.args[1].find(), arg1):
            return opt_op
    return None


def test_cse():
    var0 = getarg(0)
    var1 = getarg(1)
    var2 = add(var0, var1)
    var3 = add(var0, var1) # the same as var3
    var4 = add(var2, 2)
    var5 = add(var3, 2) # the same as var4
    var6 = add(var4, var5)

    bb = [var0, var1, var2, var3, var4, var5, var6]
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
# that replaces Operations by newly invented Operations, a simple strength
# reduction

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
    var0 = getarg(0)
    var1 = add(var0, var0)

    opt_bb = strength_reduce([var0, var1])

    assert basicblock_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = lshift(optvar0, 1)"""

# _____________________________________________________________________

# let's combine the passes

def optimize(bb: list[Operation]) -> list[Operation]:
    opt_bb = []

    for op in bb:
        if op.name == "add":
            arg0 = op.args[0].find()
            arg1 = op.args[1].find()
            if isinstance(arg0, Constant) and isinstance(arg1, Constant):
                # constant fold
                op.make_equal_to(Constant(arg0.value + arg1.value))
                continue
            # cse
            prev_op = find_prev_add_op(op, opt_bb)
            if prev_op is not None:
                op.make_equal_to(prev_op)
                continue
            # strength reduce

            # arithmetic simplification: a + 0 => a
            if eq_value(arg0, Constant(0)):
                op.make_equal_to(arg1)
                continue
            if eq_value(arg1, Constant(0)):
                op.make_equal_to(arg0)
                continue
        opt_bb.append(op)
    return opt_bb

