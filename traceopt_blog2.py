import pytest
import re
from dataclasses import dataclass
from typing import Optional, Any


class Value:
    def find(self):
        raise NotImplementedError("abstract")

@dataclass(eq=False)
class Operation(Value):
    name : str
    args : list

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

class Object:
    def __init__(self):
        self.contents: dict[int, Any] = {}

    def store(self, idx : int, value : Any):
        self.contents[idx] = value

    def load(self, idx : int):
        return self.contents[idx]

def get_num(op, index=1):
    assert isinstance(op.arg(index), Constant)
    return op.arg(index).value

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
        elif op.name == "alloc":
            res = Object()
        elif op.name == "load":
            res = argval(op, 0).load(
                get_num(op))
        elif op.name == "store":
            argval(op, 0).store(
                get_num(op), argval(op, 2))
            continue # no result
        elif op.name == "escape":
            return argval(op, 0)
        results[op] = res

def test_interpret():
    bb = Block()
    var0 = bb.getarg(0)
    ls = bb.alloc()
    sto = bb.store(ls, 0, var0)
    var1 = bb.load(ls, 0)
    bb.escape(var1)
    assert interpret(bb, 17) == 17


# version 1: always remove alloc

class VirtualObject:
    def __init__(self):
        self.contents: dict[int, Value] = {}

    def store(self, idx, value):
        self.contents[idx] = value

    def load(self, idx):
        return self.contents[idx]

def optimize_alloc_removal_1(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            field = get_num(op)
            info.store(field, op.arg(2))
            continue
        opt_bb.append(op)
    return opt_bb

def example1(optimize):
    # remove unused allocations
    bb = Block()
    var0 = bb.getarg(0)
    ls = bb.alloc()
    sto = bb.store(ls, 0, var0)
    var1 = bb.load(ls, 0)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)"""

def test_alloc_removal_1():
    example1(optimize_alloc_removal_1)


def example2(optimize):
    # keep around allocations that escape
    bb = Block()
    var0 = bb.getarg(0)
    ls = bb.alloc()
    sto = bb.store(var0, 0, ls)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = store(optvar0, 0, optvar1)"""

@pytest.mark.xfail
def test_alloc_removal_1_fail():
    example2(optimize_alloc_removal_1)


# version 2

def materialize_2(opt_bb, value: Operation) -> None:
    assert not isinstance(value, Constant)
    assert isinstance(value, Operation)
    info = value.info
    assert info
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)

def optimize_alloc_removal_2(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_2(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb


def test_alloc_removal_2():
    example1(optimize_alloc_removal_2)
    example2(optimize_alloc_removal_2)

def example3(optimize):
    # don't materialize allocations twice
    bb = Block()
    var0 = bb.getarg(0)
    ls = bb.alloc()
    sto0 = bb.store(var0, 0, ls)
    sto1 = bb.store(var0, 0, ls)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = store(optvar0, 0, optvar1)
optvar3 = store(optvar0, 0, optvar1)"""

@pytest.mark.xfail
def test_alloc_removal_2_fail():
    example3(optimize_alloc_removal_2)

# version 3 don't materialize twice

def materialize_3(opt_bb, value: Operation) -> None:
    assert not isinstance(value, Constant)
    assert isinstance(value, Operation)
    info = value.info
    if info is None:
        return # already materialized
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)
    # but only once
    value.info = None

def optimize_alloc_removal_3(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_3(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb

def example4(optimize):
    # materialization of non-virtuals
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.getarg(1)
    sto = bb.store(var0, 0, var1)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = getarg(1)
optvar2 = store(optvar0, 0, optvar1)"""


def test_alloc_removal_3():
    example1(optimize_alloc_removal_3)
    example2(optimize_alloc_removal_3)
    example3(optimize_alloc_removal_3)
    example4(optimize_alloc_removal_3)

def example5(optimize):
    # materialization of constants
    bb = Block()
    var0 = bb.getarg(0)
    sto = bb.store(var0, 0, 17)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = store(optvar0, 0, 17)"""

@pytest.mark.xfail
def test_alloc_removal_3_fail():
    example5(optimize_alloc_removal_3)

# version 4 constants

def materialize_4(opt_bb, value: Operation) -> None:
    if isinstance(value, Constant):
        return
    assert isinstance(value, Operation)
    info = value.info
    if info is None:
        return # already materialized
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)
    # but only once
    value.info = None

def optimize_alloc_removal_4(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_4(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb

def test_alloc_removal_4():
    example1(optimize_alloc_removal_4)
    example2(optimize_alloc_removal_4)
    example3(optimize_alloc_removal_4)
    example4(optimize_alloc_removal_4)
    example5(optimize_alloc_removal_4)

def example6(optimize):
    # materialize allocation contents
    bb = Block()
    var0 = bb.getarg(0)
    ls = bb.alloc()
    contents0 = bb.store(ls, 1, 8)
    contents1 = bb.store(ls, 0, 7)
    sto = bb.store(var0, 0, ls)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = store(optvar1, 0, 7)
optvar3 = store(optvar1, 1, 8)
optvar4 = store(optvar0, 0, optvar1)"""

@pytest.mark.xfail
def test_alloc_removal_4_fail():
    example6(optimize_alloc_removal_4)


# version 5 materialize content

def materialize_5(opt_bb, value: Operation) -> None:
    if isinstance(value, Constant):
        return
    assert isinstance(value, Operation)
    info = value.info
    if info is None:
        return # already materialized
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)
    # put the content back
    for idx, val in sorted(info.contents.items()):
        opt_bb.store(value, idx, val)
    # only materialize once
    value.info = None

def optimize_alloc_removal_5(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_5(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb

def test_alloc_removal_5():
    example1(optimize_alloc_removal_5)
    example2(optimize_alloc_removal_5)
    example3(optimize_alloc_removal_5)
    example4(optimize_alloc_removal_5)
    example5(optimize_alloc_removal_5)
    example6(optimize_alloc_removal_5)

def example7(optimize):
    # materialize chained objects
    bb = Block()
    var0 = bb.getarg(0)
    ls0 = bb.alloc()
    ls1 = bb.alloc()
    contents = bb.store(ls0, 1, ls1)
    const = bb.store(ls1, 2, 1337)
    sto = bb.store(var0, 0, ls0)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = alloc()
optvar3 = store(optvar2, 2, 1337)
optvar4 = store(optvar1, 1, optvar2)
optvar5 = store(optvar0, 0, optvar1)"""


@pytest.mark.xfail
def test_alloc_removal_5_fail():
    example7(optimize_alloc_removal_5)

# version 6 materialize recursively

def materialize_6(opt_bb, value: Operation) -> None:
    if isinstance(value, Constant):
        return
    assert isinstance(value, Operation)
    info = value.info
    if info is None:
        return # already materialized
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)
    # put the content back
    for idx, val in sorted(info.contents.items()):
        # materialize recursively
        materialize(opt_bb, val)
        opt_bb.store(value, idx, val)
    # only materialize once
    value.info = None

def optimize_alloc_removal_6(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_6(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb

def test_alloc_removal_6():
    example1(optimize_alloc_removal_6)
    example2(optimize_alloc_removal_6)
    example3(optimize_alloc_removal_6)
    example4(optimize_alloc_removal_6)
    example5(optimize_alloc_removal_6)
    example6(optimize_alloc_removal_6)
    example7(optimize_alloc_removal_6)

def example8(optimize):
    # handle recursive store
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.alloc()
    var2 = bb.store(var1, 0, var1)
    var3 = bb.store(var0, 1, var1)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = store(optvar1, 0, optvar1)
optvar3 = store(optvar0, 1, optvar1)"""



@pytest.mark.xfail
def test_alloc_removal_6_fail():
    example8(optimize_alloc_removal_6)

# version 7 fix recursion bug

def materialize_7(opt_bb, value: Operation) -> None:
    if isinstance(value, Constant):
        return
    assert isinstance(value, Operation)
    info = value.info
    if info is None:
        return # already materialized
    assert value.name == "alloc"
    # put the alloc operation back into the trace
    opt_bb.append(value)
    # only materialize once
    value.info = None
    # put the content back
    for idx, val in sorted(info.contents.items()):
        # materialize recursively
        materialize(opt_bb, val)
        opt_bb.store(value, idx, val)

def optimize_alloc_removal_7(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            field = get_num(op)
            op.make_equal_to(info.load(field))
            continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            else:
                materialize_7(opt_bb, op.arg(2))
        opt_bb.append(op)
    return opt_bb

def test_alloc_removal_7():
    example1(optimize_alloc_removal_7)
    example2(optimize_alloc_removal_7)
    example3(optimize_alloc_removal_7)
    example4(optimize_alloc_removal_7)
    example5(optimize_alloc_removal_7)
    example6(optimize_alloc_removal_7)
    example7(optimize_alloc_removal_7)
    example8(optimize_alloc_removal_7)


def example9(optimize):
    # materialize not just on store
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.alloc()
    var2 = bb.escape(var1)
    opt_bb = optimize(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = alloc()
optvar2 = escape(optvar1)"""


@pytest.mark.xfail
def test_alloc_removal_7_fail():
    example9(optimize_alloc_removal_7)


# final

def materialize(opt_bb, value: Value) -> None:
    if isinstance(value, Constant):
        return
    assert isinstance(value, Operation)
    info = value.info
    if not info:
        # Already materialized
        return
    assert value.name == "alloc"
    opt_bb.append(value)
    value.info = None
    for idx, val in sorted(info.contents.items()):
        materialize(opt_bb, val)
        opt_bb.store(value, idx, val)

def optimize_alloc_removal(bb):
    opt_bb = Block()
    for op in bb:
        if op.name == "alloc":
            op.info = VirtualObject()
            continue
        if op.name == "load":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                op.make_equal_to(info.load(field))
                continue
        if op.name == "store":
            info = op.arg(0).info
            if info:
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
        for arg in op.args:
            materialize(opt_bb, arg.find())
        opt_bb.append(op)
    return opt_bb


def test_alloc_removal_final():
    example1(optimize_alloc_removal)
    example2(optimize_alloc_removal)
    example3(optimize_alloc_removal)
    example4(optimize_alloc_removal)
    example5(optimize_alloc_removal)
    example6(optimize_alloc_removal)
    example7(optimize_alloc_removal)
    example8(optimize_alloc_removal)
    example9(optimize_alloc_removal)

def test_alloc_removal_final():
    # sink allocations
    bb = Block()
    var0 = bb.getarg(0)
    var1 = bb.alloc()
    var2 = bb.store(var1, 0, 123)
    var3 = bb.store(var1, 1, 456)
    var4 = bb.load(var1, 0)
    var5 = bb.load(var1, 1)
    var6 = bb.add(var4, var5)
    var7 = bb.store(var1, 0, var6)
    var8 = bb.store(var0, 1, var1)
    opt_bb = optimize_alloc_removal(bb)
    assert bb_to_str(opt_bb, "optvar") == """\
optvar0 = getarg(0)
optvar1 = add(123, 456)
optvar2 = alloc()
optvar3 = store(optvar2, 0, optvar1)
optvar4 = store(optvar2, 1, 456)
optvar5 = store(optvar0, 1, optvar2)"""

