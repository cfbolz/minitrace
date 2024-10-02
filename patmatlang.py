import sys
from contextlib import contextmanager
from collections import defaultdict
from rply import LexerGenerator, LexingError, ParserGenerator, ParsingError
from rply.token import BaseBox

from rpython.rlib.rarithmetic import LONG_BIT, r_uint, intmask, ovfcheck, uint_mul_high

# ____________________________________________________________
# lexer

lg = LexerGenerator()

alltokens = []


def addtok(name, regex):
    alltokens.append(name)
    lg.add(name, regex)


def addkeyword(kw):
    addtok(kw.upper(), r"\b" + kw + r"\b")


addkeyword("check")
addkeyword("and")
addkeyword("or")

addtok("NUMBER", r"[+-]?([1-9]\d*)|0")
addtok("NAME", r"[a-zA-Z_][a-zA-Z_0-9]*")
addtok("LSHIFT", r"[<][<]")
addtok("ARSHIFT", r"[>][>]a")
addtok("URSHIFT", r"[>][>]u")
addtok("ARROW", r"=>")
addtok("LPAREN", r"[(]")
addtok("RPAREN", r"[)]")
addtok("COMMA", r"[,]")
addtok("EQUALEQUAL", r"[=][=]")
addtok("EQUAL", r"[=]")
addtok("COLON", r"[:]")
addtok("DOT", r"[.]")
addtok("GE", r"[>][=]")
addtok("GT", r"[>]")
addtok("LE", r"[<][=]")
addtok("LT", r"[<]")
addtok("NE", r"[!=]")

addtok("PLUS", r"[+]")
addtok("MINUS", r"[-]")
addtok("MUL", r"[*]")
addtok("DIV", r"[/][/]")
addtok("OP_AND", r"[&]")
addtok("OP_OR", r"[|]")
addtok("OP_XOR", r"^")
addtok("INVERT", r"~")

addtok("NEWLINE", r" *([#].*)?\n")

lg.ignore(r"[ ]")

lexer = lg.build()


# ____________________________________________________________
# AST classes


class Visitor(object):
    def visit(self, ast):
        meth = getattr(self, "visit_%s" % type(ast).__name__, None)
        if meth is not None:
            return meth(ast)
        return self.default_visit(ast)

    def default_visit(self, ast):
        pass


class BaseAst(BaseBox):
    # __metaclass__ = extendabletype

    def __eq__(self, other):
        if type(self) != type(other):
            return NotImplemented
        return self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        args = ["%s=%r" % (key, value) for key, value in self.__dict__.items()]
        if len(args) == 1:
            args = [repr(self.__dict__.values()[0])]
        return "%s(%s)" % (
            type(self).__name__,
            ", ".join(args),
        )

    def view(self):
        from rpython.translator.tool.make_dot import DotGen
        from dotviewer import graphclient
        import pytest

        dotgen = DotGen("G")
        self._dot(dotgen)
        p = pytest.ensuretemp("pyparser").join("temp.dot")
        p.write(dotgen.generate(target=None))
        graphclient.display_dot_file(str(p))

    def _dot(self, dotgen):
        arcs = []
        label = [type(self).__name__]
        for key, value in self.__dict__.items():
            if isinstance(value, BaseAst):
                arcs.append((value, key))
                value._dot(dotgen)
            elif isinstance(value, list) and value and isinstance(value[0], BaseAst):
                for index, item in enumerate(value):
                    arcs.append((item, "%s[%s]" % (key, index)))
                    item._dot(dotgen)
            else:
                label.append("%s = %r" % (key, value))
        dotgen.emit_node(str(id(self)), shape="box", label="\n".join(label))
        for target, label in arcs:
            dotgen.emit_edge(str(id(self)), str(id(target)), label)


class File(BaseAst):
    def __init__(self, rules):
        self.rules = rules


class Rule(BaseAst):
    def __init__(self, name, pattern, elements, target):
        self.name = name
        self.pattern = pattern
        self.elements = elements
        self.target = target

    def __str__(self):
        lines = [self.name + ": " + str(self.pattern)]
        for el in self.elements:
            lines.append("    " + str(el))
        lines.append("    => " + str(self.target))
        return "\n".join(lines)


class Pattern(BaseAst):
    pass


class PatternVar(Pattern):
    def __init__(self, name):
        self.name = name

    def sort_key(self):
        return (3, self.name)

    def __str__(self):
        return self.name


class PatternConst(BaseAst):
    def __init__(self, const):
        self.const = const

    def sort_key(self):
        return (0, self.const)

    def __str__(self):
        return str(self.const)


class PatternOp(BaseAst):
    def __init__(self, opname, args):
        self.opname = opname
        self.args = args

    def newargs(self, args):
        return PatternOp(self.opname, args)

    def sort_key(self):
        return (1, self.opname) + tuple(sorted(arg.sort_key() for arg in self.args))

    def __str__(self):
        return "%s(%s)" % (self.opname, ", ".join([str(arg) for arg in self.args]))


class Compute(BaseAst):
    def __init__(self, name, expr):
        self.name = name
        self.expr = expr

    def __str__(self):
        return "compute %s = %s" % (self.name, self.expr)


class Check(BaseAst):
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "check %s" % (self.expr,)


class Expression(BaseAst):
    pass


class Name(BaseAst):
    def __init__(self, name):
        self.name = name


class Number(BaseAst):
    def __init__(self, value):
        self.value = value


class BinOp(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class IntBinOp(BinOp):
    pass


class Add(IntBinOp):
    opname = "int_add"


class Sub(IntBinOp):
    opname = "int_sub"


class Mul(IntBinOp):
    opname = "int_mul"


class Div(IntBinOp):
    opname = "int_div"


class LShift(IntBinOp):
    opname = "int_lshift"


class URShift(IntBinOp):
    opname = "uint_rshift"


class ARShift(IntBinOp):
    opname = "int_rshift"


class OpAnd(IntBinOp):
    opname = "int_and"


class OpOr(IntBinOp):
    opname = "int_or"


class OpXor(IntBinOp):
    opname = "int_xor"


class Eq(IntBinOp):
    opname = "int_eq"


class Ge(IntBinOp):
    opname = "int_ge"


class Gt(IntBinOp):
    opname = "int_gt"


class Le(IntBinOp):
    opname = "int_le"


class Lt(IntBinOp):
    opname = "int_lt"


class Ne(IntBinOp):
    opname = "int_ne"


class ShortcutAnd(BinOp):
    pass


class ShortcutOr(BinOp):
    pass


class UnaryOp(Expression):
    def __init__(self, left):
        self.left = left


class IntUnaryOp(UnaryOp):
    pass


class Invert(IntUnaryOp):
    opname = "int_invert"


class Attribute(BaseAst):
    def __init__(self, varname, attrname):
        self.varname = varname
        self.attrname = attrname


class MethodCall(BaseAst):
    def __init__(self, value, methname, args):
        self.value = value
        self.methname = methname
        self.args = args


class FuncCall(BaseAst):
    def __init__(self, funcname, args):
        self.funcname = funcname
        self.args = args


# ____________________________________________________________
# parser

pg = ParserGenerator(
    alltokens,
    precedence=[
        ("left", ["OR"]),
        ("left", ["AND"]),
        ("left", ["NOT"]),
        ("left", ["EQUALEQUAL", "GE", "GT", "LE", "LT", "NE"]),
        ("left", ["OP_OR"]),
        ("left", ["OP_XOR"]),
        ("left", ["OP_AND"]),
        ("left", ["LSHIFT", "ARSHIFT", "URSHIFT"]),
        ("left", ["PLUS", "MINUS"]),
        ("left", ["MUL", "DIV"]),
        ("left", ["INVERT"]),
        ("left", ["DOT"]),
    ],
)


@pg.production("file : rule | file rule")
def file(p):
    if len(p) == 1:
        return File(p)
    return File(p[0].rules + [p[1]])


@pg.production("newlines : NEWLINE | NEWLINE newlines")
def newlines(p):
    return None


@pg.production("rule : NAME COLON pattern elements ARROW pattern newlines")
def rule(p):
    return Rule(p[0].value, p[2], p[3], p[5])


@pg.production("pattern : NAME")
def pattern_var(p):
    return PatternVar(p[0].value)


@pg.production("pattern : NUMBER")
def pattern_const(p):
    return PatternConst(p[0].value)


@pg.production("pattern : NAME LPAREN patternargs RPAREN")
def pattern_op(p):
    return PatternOp(p[0].value, p[2])


@pg.production("patternargs : pattern | pattern COMMA patternargs")
def patternargs(p):
    if len(p) == 1:
        return p
    return [p[0]] + p[2]


@pg.production("elements : newlines | newlines element elements")
def elements(p):
    if len(p) == 1:
        return []
    return [p[1]] + p[2]


@pg.production("element : NAME EQUAL expression")
def compute_element(p):
    return Compute(p[0].value, p[2])


@pg.production("element : CHECK expression")
def check(p):
    return Check(p[1])


@pg.production("expression : NUMBER")
def expression_number(p):
    return Number(int(p[0].getstr()))


@pg.production("expression : NAME")
def expression_name(p):
    return Name(p[0].getstr())


@pg.production("expression : LPAREN expression RPAREN")
def expression_parens(p):
    return p[1]


@pg.production("expression : INVERT expression")
def expression_unary(p):
    return Invert(p[1])


@pg.production("expression : expression PLUS expression")
@pg.production("expression : expression MINUS expression")
@pg.production("expression : expression MUL expression")
@pg.production("expression : expression DIV expression")
@pg.production("expression : expression LSHIFT expression")
@pg.production("expression : expression URSHIFT expression")
@pg.production("expression : expression ARSHIFT expression")
@pg.production("expression : expression AND expression")
@pg.production("expression : expression OR expression")
@pg.production("expression : expression OP_AND expression")
@pg.production("expression : expression OP_OR expression")
@pg.production("expression : expression OP_XOR expression")
@pg.production("expression : expression EQUALEQUAL expression")
@pg.production("expression : expression GE expression")
@pg.production("expression : expression GT expression")
@pg.production("expression : expression LE expression")
@pg.production("expression : expression LT expression")
@pg.production("expression : expression NE expression")
def expression_binop(p):
    left = p[0]
    right = p[2]
    if p[1].gettokentype() == "PLUS":
        return Add(left, right)
    elif p[1].gettokentype() == "MINUS":
        return Sub(left, right)
    elif p[1].gettokentype() == "MUL":
        return Mul(left, right)
    elif p[1].gettokentype() == "DIV":
        return Div(left, right)
    elif p[1].gettokentype() == "LSHIFT":
        return LShift(left, right)
    elif p[1].gettokentype() == "URSHIFT":
        return URShift(left, right)
    elif p[1].gettokentype() == "ARSHIFT":
        return ARShift(left, right)
    elif p[1].gettokentype() == "AND":
        return ShortcutAnd(left, right)
    elif p[1].gettokentype() == "OR":
        return ShortcutOr(left, right)
    elif p[1].gettokentype() == "OP_AND":
        return OpAnd(left, right)
    elif p[1].gettokentype() == "OP_OR":
        return OpOr(left, right)
    elif p[1].gettokentype() == "OP_XOR":
        return OpXor(left, right)
    elif p[1].gettokentype() == "EQUALEQUAL":
        return Eq(left, right)
    elif p[1].gettokentype() == "GE":
        return Ge(left, right)
    elif p[1].gettokentype() == "GT":
        return Gt(left, right)
    elif p[1].gettokentype() == "LE":
        return Le(left, right)
    elif p[1].gettokentype() == "LT":
        return Lt(left, right)
    elif p[1].gettokentype() == "NE":
        return Ne(left, right)
    else:
        raise AssertionError("Oops, this should not be possible!")


@pg.production("expression : expression DOT NAME maybecall")
def attr_or_method(p):
    assert p[1].gettokentype() == "DOT"
    if p[3] is not None:
        return MethodCall(p[0], p[2].value, p[3])
    return Attribute(p[0].name, p[2].value)


@pg.production("expression : NAME LPAREN args RPAREN")
def funccall(p):
    return FuncCall(p[0].value, p[2])


@pg.production("maybecall : | LPAREN args RPAREN")
def methodcall(p):
    if not p:
        return None
    return p[1]


@pg.production("args : | expression | expression COMMA args ")
def args(p):
    if len(p) <= 1:
        return p
    import pdb

    pdb.set_trace()


parser = pg.build()


def print_conflicts():
    if parser.lr_table.rr_conflicts:
        print("rr conflicts")
    for rule_num, token, conflict in parser.lr_table.rr_conflicts:
        print(rule_num, token, conflict)

    if parser.lr_table.sr_conflicts:
        print("sr conflicts")
    for rule_num, token, conflict in parser.lr_table.sr_conflicts:
        print(rule_num, token, conflict)


parser = pg.build()
print_conflicts()


def parse(s):
    return parser.parse(lexer.lex(s))


def test_parse_int_add_zero():
    s = """\
add_zero: int_add(x, 0)
    => x
"""
    ast = parse(s)
    assert ast == File(
        rules=[
            Rule(
                elements=[],
                name="add_zero",
                pattern=PatternOp(
                    args=[PatternVar(name="x"), PatternConst(const="0")],
                    opname="int_add",
                ),
                target=PatternVar(name="x"),
            )
        ]
    )


def test_parse_int_add_zero():
    s = """\
add_reassoc_consts: int_add(int_add(x, C1), C2)
    C = C1 + C2
    => int_add(x, C)
"""
    ast = parse(s)
    assert ast == File(
        rules=[
            Rule(
                elements=[
                    Compute(
                        expr=Add(left=Name(name="C1"), right=Name(name="C2")), name="C"
                    )
                ],
                name="add_reassoc_consts",
                pattern=PatternOp(
                    args=[
                        PatternOp(
                            args=[PatternVar(name="x"), PatternVar(name="C1")],
                            opname="int_add",
                        ),
                        PatternVar(name="C2"),
                    ],
                    opname="int_add",
                ),
                target=PatternOp(
                    args=[PatternVar(name="x"), PatternVar(name="C")], opname="int_add"
                ),
            )
        ]
    )


def test_parse_int_mul():
    s = """\
mul_zero: int_mul(x, 0)
    => 0

mul_one: int_mul(x, 1)
    => 1

mul_minus_one: int_mul(x, -1)
    => int_neg(x)

mul_neg_neg: int_mul(int_neg(x), int_neg(y))
    => int_mul(x, y)
"""
    ast = parse(s)
    assert ast == File(
        rules=[
            Rule(
                elements=[],
                name="mul_zero",
                pattern=PatternOp(
                    args=[PatternVar(name="x"), PatternConst(const="0")],
                    opname="int_mul",
                ),
                target=PatternConst(const="0"),
            ),
            Rule(
                elements=[],
                name="mul_one",
                pattern=PatternOp(
                    args=[PatternVar(name="x"), PatternConst(const="1")],
                    opname="int_mul",
                ),
                target=PatternConst(const="1"),
            ),
            Rule(
                elements=[],
                name="mul_minus_one",
                pattern=PatternOp(
                    args=[PatternVar(name="x"), PatternConst(const="-1")],
                    opname="int_mul",
                ),
                target=PatternOp(args=[PatternVar(name="x")], opname="int_neg"),
            ),
            Rule(
                elements=[],
                name="mul_neg_neg",
                pattern=PatternOp(
                    args=[
                        PatternOp(args=[PatternVar(name="x")], opname="int_neg"),
                        PatternOp(args=[PatternVar(name="y")], opname="int_neg"),
                    ],
                    opname="int_mul",
                ),
                target=PatternOp(
                    args=[PatternVar(name="x"), PatternVar(name="y")], opname="int_mul"
                ),
            ),
        ]
    )


def test_parse_lshift_rshift():
    s = """\
int_lshift_int_rshift_consts: int_lshift(int_rshift(x, C1), C1)
    C = (-1 >>a C1) << C1
    => int_and(x, C)
    """
    ast = parse(s)


def generate_commutative_patterns_args(args):
    if not args:
        yield []
        return
    arg0 = args[0]
    args1 = args[1:]
    for subarg0 in generate_commutative_patterns(arg0):
        for subargs1 in generate_commutative_patterns_args(args1):
            yield [arg0] + subargs1


def generate_commutative_patterns(pattern):
    if not isinstance(pattern, PatternOp):
        yield pattern
        return
    for subargs in generate_commutative_patterns_args(pattern.args):
        if pattern.opname not in commutative_ops:
            yield pattern.newargs(subargs)
        else:
            yield pattern.newargs(subargs)
            yield pattern.newargs(subargs[::-1])


def test_generate_commutative_rules():
    s = """\
add_zero: int_add(x, 0)
    => x
"""
    ast = parse(s)
    patterns = list(generate_commutative_patterns(ast.rules[0].pattern))
    assert patterns == [
        PatternOp(
            args=[PatternVar(name="x"), PatternConst(const="0")], opname="int_add"
        ),
        PatternOp(
            args=[PatternConst(const="0"), PatternVar(name="x")], opname="int_add"
        ),
    ]
    assert len(patterns) == 2

    s = """\
add_reassoc_consts: int_add(int_add(x, C1), C2)
    C = C1 + C2
    => int_add(x, C)
"""
    ast = parse(s)
    patterns = list(generate_commutative_patterns(ast.rules[0].pattern))
    assert patterns == [
        PatternOp(
            opname="int_add",
            args=[
                PatternOp(opname="int_add", args=[PatternVar("x"), PatternVar("C1")]),
                PatternVar("C2"),
            ],
        ),
        PatternOp(
            opname="int_add",
            args=[
                PatternVar("C2"),
                PatternOp(opname="int_add", args=[PatternVar("x"), PatternVar("C1")]),
            ],
        ),
        PatternOp(
            opname="int_add",
            args=[
                PatternOp(opname="int_add", args=[PatternVar("x"), PatternVar("C1")]),
                PatternVar("C2"),
            ],
        ),
        PatternOp(
            opname="int_add",
            args=[
                PatternVar("C2"),
                PatternOp(opname="int_add", args=[PatternVar("x"), PatternVar("C1")]),
            ],
        ),
    ]


def sort_rules(rules):
    return sorted(rules, key=lambda rule: rule.pattern.sort_key())


def test_sort_patterns():
    s = """\
int_sub_zero: int_sub(x, 0)
    => x
int_sub_x_x: int_sub(x, x)
    => 0
int_sub_add: int_sub(int_add(x, y), y)
    => x
int_sub_zero_neg: int_sub(0, x)
    => int_neg(x)
    """
    ast = parse(s)
    rules = sort_rules(ast.rules)
    assert rules == [
        Rule(
            name="int_sub_zero",
            pattern=PatternOp(
                opname="int_sub", args=[PatternVar("x"), PatternConst("0")]
            ),
            elements=[],
            target=PatternVar("x"),
        ),
        Rule(
            name="int_sub_zero_neg",
            pattern=PatternOp(
                opname="int_sub", args=[PatternConst("0"), PatternVar("x")]
            ),
            elements=[],
            target=PatternOp(opname="int_neg", args=[PatternVar("x")]),
        ),
        Rule(
            name="int_sub_add",
            pattern=PatternOp(
                opname="int_sub",
                args=[
                    PatternOp(
                        opname="int_add", args=[PatternVar("x"), PatternVar("y")]
                    ),
                    PatternVar("y"),
                ],
            ),
            elements=[],
            target=PatternVar("x"),
        ),
        Rule(
            name="int_sub_x_x",
            pattern=PatternOp(
                opname="int_sub", args=[PatternVar("x"), PatternVar("x")]
            ),
            elements=[],
            target=PatternConst("0"),
        ),
    ]


commutative_ops = {"int_add", "int_mul"}

# ___________________________________________________________________________

import z3
from rpython.jit.metainterp.optimizeopt.test.test_z3intbound import (
    Z3IntBound,
    make_z3_intbounds_instance,
)


class CouldNotProve(Exception):
    pass


TRUEBV = z3.BitVecVal(1, LONG_BIT)
FALSEBV = z3.BitVecVal(0, LONG_BIT)


def z3_cond(z3expr):
    return z3.If(z3expr, TRUEBV, FALSEBV)


def z3_bool_expression(opname, arg0, arg1=None):
    expr = None
    valid = True
    if opname == "int_eq":
        expr = arg0 == arg1
    elif opname == "int_ne":
        expr = arg0 != arg1
    elif opname == "int_lt":
        expr = arg0 < arg1
    elif opname == "int_le":
        expr = arg0 <= arg1
    elif opname == "int_gt":
        expr = arg0 > arg1
    elif opname == "int_ge":
        expr = arg0 >= arg1
    elif opname == "uint_lt":
        expr = z3.ULT(arg0, arg1)
    elif opname == "uint_le":
        expr = z3.ULE(arg0, arg1)
    elif opname == "uint_gt":
        expr = z3.UGT(arg0, arg1)
    elif opname == "uint_ge":
        expr = z3.UGE(arg0, arg1)
    elif opname == "int_is_true":
        expr = arg0 != FALSEBV
    elif opname == "int_is_zero":
        expr = arg0 == FALSEBV
    else:
        assert 0
    return expr, valid


def z3_expression(opname, arg0, arg1=None):
    expr = None
    valid = True
    if opname == "int_add":
        expr = arg0 + arg1
    elif opname == "int_sub":
        expr = arg0 - arg1
    elif opname == "int_mul":
        expr = arg0 * arg1
    elif opname == "int_and":
        expr = arg0 & arg1
    elif opname == "int_or":
        expr = arg0 | arg1
    elif opname == "int_xor":
        expr = arg0 ^ arg1
    elif opname == "int_lshift":
        expr = arg0 << arg1
        valid = z3.And(arg1 >= 0, arg1 < LONG_BIT)
    elif opname == "int_rshift":
        expr = arg0 >> arg1
        valid = z3.And(arg1 >= 0, arg1 < LONG_BIT)
    elif opname == "uint_rshift":
        expr = z3.LShR(arg0, arg1)
        valid = z3.And(arg1 >= 0, arg1 < LONG_BIT)
    elif opname == "uint_mul_high":
        # zero-extend args to 2*LONG_BIT bit, then multiply and extract
        # highest LONG_BIT bits
        zarg0 = z3.ZeroExt(LONG_BIT, arg0)
        zarg1 = z3.ZeroExt(LONG_BIT, arg1)
        expr = z3.Extract(LONG_BIT * 2 - 1, LONG_BIT, zarg0 * zarg1)
    elif opname == "int_neg":
        expr = -arg0
    elif opname == "int_invert":
        expr = ~arg0
    else:
        expr, valid = z3_bool_expression(opname, arg0, arg1)
        return z3_cond(expr), valid
    return expr, valid


def z3_and(*args):
    args = [arg for arg in args if arg is not True]
    if args:
        if len(args) == 1:
            return args[0]
        return z3.And(*args)
    return True


def z3_implies(a, b):
    if a is True:
        return b
    return z3.Implies(a, b)

def popcount64(w):
    w -= (w >> 1) & 0x5555555555555555
    w = (w & 0x3333333333333333) + ((w >> 2) & 0x3333333333333333)
    w = (w + (w >> 4)) & 0x0f0f0f0f0f0f0f0f
    return ((w * 0x0101010101010101) >> 56) & 0xff

def highest_bit(x):
    x |= x >> 1
    x |= x >> 2
    x |= x >> 4
    x |= x >> 8
    x |= x >> 16
    x |= x >> 32
    return popcount64(x) - 1

def z3_highest_bit(x):
    x |= z3.LShR(x, 1)
    x |= z3.LShR(x, 2)
    x |= z3.LShR(x, 4)
    x |= z3.LShR(x, 8)
    x |= z3.LShR(x, 16)
    x |= z3.LShR(x, 32)
    return popcount64(x) - 1

def test_higest_bit():
    for i in range(64):
        assert highest_bit(r_uint(1) << i) == i

class Prover(object):
    def __init__(self):
        self.solver = z3.Solver()
        self.name_to_z3 = {}
        self.name_to_intbound = {}
        self.glue_conditions_added = set()
        self.glue_conditions = []

    def prove(self, cond):
        z3res = self.solver.check(z3.Not(cond))
        if z3res == z3.unsat:
            return True
        elif z3res == z3.unknown:
            return False
        elif z3res == z3.sat:
            global model
            model = self.solver.model()
            return False

    def _convert_var(self, name):
        def newvar(name, suffix=""):
            if suffix:
                name += "_" + suffix
            res = z3.BitVec(name, LONG_BIT)
            self.name_to_z3[name] = res
            return res

        if name in self.name_to_z3:
            return self.name_to_z3[name]
        res = newvar(name)
        b = make_z3_intbounds_instance(name, res)
        self.name_to_intbound[name] = b
        return res

    def _convert_intbound(self, name):
        b = self.name_to_intbound[name]
        if name not in self.glue_conditions_added:
            self.glue_conditions.append(b.z3_formula())
            self.glue_conditions_added.add(name)
        return b

    def _convert_attr(
        self,
        varname,
        attrname,
    ):
        b = self._convert_intbound(varname)
        return getattr(b, attrname)

    def convert_pattern(self, pattern):
        if isinstance(pattern, PatternOp):
            args = [self.convert_pattern(arg) for arg in pattern.args]
            res, valid = z3_expression(pattern.opname, *[arg[0] for arg in args])
            return res, z3_and(valid, *[arg[1] for arg in args])

        if isinstance(pattern, PatternVar):
            return self._convert_var(pattern.name), True
        if isinstance(pattern, PatternConst):
            res = z3.BitVecVal(pattern.const, LONG_BIT)
            return res, True
        import pdb

        pdb.set_trace()

    def convert_expr(self, expr, targettype=int):
        if isinstance(expr, IntBinOp):
            left, leftvalid = self.convert_expr(expr.left, int)
            right, rightvalid = self.convert_expr(expr.right, int)
            if targettype is int:
                res, valid = z3_expression(expr.opname, left, right)
            else:
                assert targettype is bool
                res, valid = z3_bool_expression(expr.opname, left, right)
            return res, z3_and(leftvalid, rightvalid, valid)
        if isinstance(expr, IntUnaryOp):
            assert targettype is int
            left, leftvalid = self.convert_expr(expr.left, targettype)
            res, valid = z3_expression(expr.opname, left)
            return res, z3_and(leftvalid, valid)
        if isinstance(expr, Name):
            if expr.name == 'LONG_BIT':
                return 64, True
            if expr.name == 'MAXINT':
                return MAXINT, True
            if expr.name == 'MININT':
                return MININT, True
            var = self._convert_var(expr.name)
            if targettype is int:
                return var, True
            if targettype is Z3IntBound:
                b = self._convert_intbound(expr.name)
                return b, True
            import pdb

            pdb.set_trace()
        if isinstance(expr, Number):
            assert targettype is int
            res = z3.BitVecVal(expr.value, LONG_BIT)
            return res, True
        if isinstance(expr, ShortcutOr):
            assert targettype is bool
            left, leftvalid = self.convert_expr(expr.left, bool)
            right, rightvalid = self.convert_expr(expr.right, bool)
            res = z3.If(left, left, right)
            return res, z3_and(leftvalid, rightvalid)
        if isinstance(expr, ShortcutAnd):
            assert targettype is bool
            left, leftvalid = self.convert_expr(expr.left, bool)
            right, rightvalid = self.convert_expr(expr.right, bool)
            res = z3.If(left, right, left)
            return res, z3_and(leftvalid, rightvalid)
        if isinstance(expr, Attribute):
            res = self._convert_attr(expr.varname, expr.attrname)
            return res, True
        if isinstance(expr, MethodCall):
            res, resvalid = self.convert_expr(expr.value, Z3IntBound)
            assert isinstance(res, Z3IntBound)
            if expr.methname in ("known_eq_const", "known_le_const", "known_ge_const"):
                targettypes = [int]
            else:
                targettypes = [Z3IntBound] * len(expr.args)
            args = [
                self.convert_expr(arg, typ) for arg, typ in zip(expr.args, targettypes)
            ]
            methargs = [arg[0] for arg in args]
            return getattr(res, expr.methname)(*methargs), z3_and(
                resvalid, *[arg[1] for arg in args]
            )
        if isinstance(expr, FuncCall):
            targettypes = [int] * len(expr.args)
            args = [
                self.convert_expr(arg, typ) for arg, typ in zip(expr.args, targettypes)
            ]
            func = globals()['z3_' + expr.funcname]
            funcargs = [arg[0] for arg in args]
            return func(*funcargs), z3_and(
                *[arg[1] for arg in args]
            )


        import pdb

        pdb.set_trace()

    def check_rule(self, rule):
        lhs, lhsvalid = self.convert_pattern(rule.pattern)
        rhs, rhsvalid = self.convert_pattern(rule.target)
        implies_left = [lhsvalid]
        implies_right = [rhsvalid, rhs == lhs]
        for el in rule.elements:
            if isinstance(el, Compute):
                expr, exprvalid = self.convert_expr(el.expr, int)
                implies_left.append(self._convert_var(el.name) == expr)
                implies_right.append(exprvalid)
                continue
            if isinstance(el, Check):
                expr, _ = self.convert_expr(el.expr, bool)
                implies_left.append(expr)
                continue
            import pdb

            pdb.set_trace()
        implies_left.extend(self.glue_conditions)
        condition = z3_implies(z3_and(*implies_left), z3_and(*implies_right))
        print("checking %s" % rule)
        print(condition)
        assert self.prove(condition)


def prove_source(s):
    for rule in parse(s).rules:
        p = Prover()
        p.check_rule(rule)


def test_z3_prove():
    s = """\
add_zero: int_add(x, 0)
    => x

add_reassoc_consts: int_add(int_add(x, C1), C2)
    C = C1 + C2
    => int_add(x, C)

sub_zero: int_sub(x, 0)
    => x

sub_from_zero: int_sub(0, x)
    => int_neg(x)

sub_x_x: int_sub(x, x)
    => 0

sub_add: int_sub(int_add(x, y), y)
    => x

lshift_rshift_c_c: int_lshift(int_rshift(x, C1), C1)
    C = (-1 >>a C1) << C1
    => int_and(x, C)

lshift_lshift_c_c: int_lshift(int_lshift(x, C1), C2)
    check 0 <= C1 and C1 < LONG_BIT and 0 <= C2 < LONG_BIT
    C = C1 + C2
    check C < LONG_BIT
    => int_lshift(x, C)

neg_neg: int_neg(int_neg(x))
    => x

invert_invert: int_invert(int_invert(x))
    => x

or_minus_1: int_or(x, -1)
    => -1

or_x_x: int_or(a, a)
    => a

or_absorb: int_or(a, int_or(a, b))
    => int_or(a, b)

and_zero: int_and(a, 0)
    => 0

and_x_x: int_and(a, a)
    => a

and_minus_1: int_and(x, -1)
    => x

and_x_c_in_range: int_and(x, C)
    check x.lower >= 0 and x.upper <= C & ~(C + 1)
    => x

and_x_y_covered_ones: int_and(x, y)
    check ~y.tvalue & (x.tmask | x.tvalue) == 0
    => x

and_known_result: int_and(a, b)
    check a.and_bound(b).is_constant()
    C = a.and_bound(b).get_constant_int()
    => C


xor_x_x: int_xor(a, a)
    => 0

xor_absorb: int_xor(int_xor(a, b), b)
    => a

xor_zero: int_xor(a, 0)
    => a

xor_minus_1: int_xor(x, -1)
    => int_invert(x)

xor_x_y_sub_y: int_sub(int_xor(x, y), y)
    # (x ^ y) - y == x if x & y == 0
    check x.and_bound(y).known_eq_const(0)
    => x

mul_zero: int_mul(x, 0)
    => 0

mul_one: int_mul(x, 1)
    => x

mul_minus_one: int_mul(x, -1)
    => int_neg(x)

mul_neg_neg: int_mul(int_neg(x), int_neg(y))
    => int_mul(x, y)

mul_lshift: int_mul(x, int_lshift(1, y))
    check y.known_ge_const(0) and y.known_le_const(LONG_BIT)
    => int_lshift(x, y)

mul_pow2_const: int_mul(x, C)
    check C > 0 and C & (C - 1) == 0
    shift = highest_bit(C)
    => int_lshift(x, shift)
"""
    prove_source(s)


# ___________________________________________________________________________


class Codegen(object):
    def __init__(self):
        self.code = []
        self.level = 0

    @contextmanager
    def emit_indent(self, line=None):
        if line is not None:
            self.emit(line)
        self.level += 1
        yield
        self.level -= 1

    def emit_stacking_condition(self, cond):
        self.emit("if %s:" % cond)
        self.level += 1

    def emit(self, line=""):
        if self.level == 0 and line.startswith(("def ", "class ")):
            self.code.append("")
        if not line.strip():
            self.code.append("")
        else:
            self.code.append("    " * self.level + line)


    def generate_code_pattern(self, p, varname, intbound_name):
        if isinstance(p, PatternVar):
            if p.name not in self.bindings:
                self.bindings[p.name] = varname
                return
            elif varname == self.bindings[p.name]:
                return
            return self.emit_stacking_condition("%s is %s" % (varname, self.bindings[p.name]))
        elif isinstance(p, PatternConst):
            return self.emit_stacking_condition("%s.known_eq_const(%s)" % (intbound_name, p.const))
        if isinstance(p, PatternOp):
            boxname = "%s_%s" % (varname, p.opname)
            self.emit("%s = self.optimizer.as_operation(%s, rop.%s)" % (boxname, varname, p.opname.upper()))
            self.emit_stacking_condition("%s is not None" % boxname)
            boxnames, boundnames = self._emit_arg_reads(boxname, varname, len(p.args))
            self._pattern_arg_check(boxnames, boundnames, p.args)
            return
        assert 0


    def generate_target(self, target):
        if isinstance(target, PatternVar):
            return "self.make_equal_to(op, %s)" % self.bindings[target.name]
        if isinstance(target, PatternConst):
            return "self.make_constant_int(op, %s)" % target.const
        if isinstance(target, PatternOp):
            import pdb;pdb.set_trace()
            return
        import pdb

        pdb.set_trace()

    def _pattern_arg_check(self, boxnames, boundnames, args):
        for i, p in enumerate(args):
            self.generate_code_pattern(p, boxnames[i], boundnames[i])

    def _emit_arg_reads(self, prefix, opname, numargs):
        boxnames = []
        boundnames = []
        for i in range(numargs):
            boxname = "%s_%s" % (prefix, i)
            boundname = "b_" + boxname
            boxnames.append(boxname)
            boundnames.append(boundname)
            self.emit("%s = get_box_replacement(%s.getarg(%s))" % (boxname, opname, i))
            self.emit("%s = self.getintbound(%s)" % (boundname, boxname))
        return boxnames, boundnames

    def generate_method(self, opname, rules):
        self.bindings = {}
        with self.emit_indent("def optimize_%s(self, op):" % opname.upper()):
            numargs = len(rules[0].pattern.args)
            boxnames, boundnames = self._emit_arg_reads("arg", "op", numargs)
            for rule in rules:
                self.emit("# %s => %s" % (rule.pattern, rule.target))
                currlevel = self.level
                checks = []
                self._pattern_arg_check(boxnames, boundnames, rule.pattern.args)
                for el in rule.elements:
                    assert 0
                targetcomp = self.generate_target(rule.target)
                self.emit("%s" % targetcomp)
                self.emit("return")
                self.level = currlevel

    def generate_code(self, ast):
        per_op = defaultdict(list)
        for rule in ast.rules:
            per_op[rule.pattern.opname].append(rule)
        for opname, rules in per_op.items():
            self.generate_method(opname, rules)
        self.emit()
        return "\n".join(self.code)


def test_generate_code():
    s = """\
int_sub_zero: int_sub(x, 0)
    => x
int_sub_x_x: int_sub(x, x)
    => 0
int_sub_add: int_sub(int_add(x, y), y)
    => x
"""
    """
int_sub_zero_neg: int_sub(0, x)
    => int_neg(x)
    """
    codegen = Codegen()
    res = codegen.generate_code(parse(s))
    assert res == """
def optimize_INT_SUB(self, op):
    arg_0 = get_box_replacement(op.getarg(0))
    b_arg_0 = self.getintbound(arg_0)
    arg_1 = get_box_replacement(op.getarg(1))
    b_arg_1 = self.getintbound(arg_1)
    # int_sub(x, 0) => x
    if b_arg_1.known_eq_const(0):
        self.make_equal_to(op, arg_0)
        return
    # int_sub(x, x) => 0
    if arg_1 is arg_0:
        self.make_constant_int(op, 0)
        return
    # int_sub(int_add(x, y), y) => x
    arg_0_int_add = self.optimizer.as_operation(arg_0, rop.INT_ADD)
    if arg_0_int_add is not None:
        arg_0_int_add_0 = get_box_replacement(arg_0.getarg(0))
        b_arg_0_int_add_0 = self.getintbound(arg_0_int_add_0)
        arg_0_int_add_1 = get_box_replacement(arg_0.getarg(1))
        b_arg_0_int_add_1 = self.getintbound(arg_0_int_add_1)
        if arg_0_int_add_0 is arg_0:
            if arg_1 is arg_0_int_add_1:
                self.make_equal_to(op, arg_0)
                return
"""


def print_class(name, *attrs):
    body = "\n        ".join(["self.%s = %s" % (attr, attr) for attr in attrs])
    print(
        """\
class %s(BaseAst):
    def __init__(self, %s):
        %s
"""
        % (name, ", ".join(attrs), body)
    )
