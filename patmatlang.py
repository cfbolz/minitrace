import sys
from contextlib import contextmanager
from collections import defaultdict
from rply import LexerGenerator, LexingError, ParserGenerator, ParsingError
from rply.token import BaseBox


# ____________________________________________________________
# lexer

lg = LexerGenerator()

alltokens = []


def addtok(name, regex):
    alltokens.append(name)
    lg.add(name, regex)


def addkeyword(kw):
    addtok(kw.upper(), kw)


addkeyword("compute")

addtok("NUMBER", r"[+-]?([1-9]\d*)|0")
addtok("NAME", r"[a-zA-Z_][a-zA-Z_0-9]*")
addtok("ARROW", r"=>")
addtok("LPAREN", r"[(]")
addtok("RPAREN", r"[)]")
addtok("COMMA", r"[,]")
addtok("EQUAL", r"[=]")
addtok("COLON", r"[:]")

addtok("PLUS", r"[+]")
addtok("MINUS", r"[-]")
addtok("MUL", r"[*]")
addtok("DIV", r"[/][/]")

addtok("NEWLINE", r"\n")

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


class Pattern(BaseAst):
    pass


class PatternVar(Pattern):
    def __init__(self, name):
        self.name = name

    def sort_key(self):
        return (3, self.name)


class PatternConst(BaseAst):
    def __init__(self, const):
        self.const = const

    def sort_key(self):
        return (0, self.const)


class PatternOp(BaseAst):
    def __init__(self, opname, args):
        self.opname = opname
        self.args = args

    def newargs(self, args):
        return PatternOp(self.opname, args)

    def sort_key(self):
        return (1, self.opname) + tuple(sorted(arg.sort_key() for arg in self.args))


class Compute(BaseAst):
    def __init__(self, name, expr):
        self.name = name
        self.expr = expr


class If(BaseAst):
    def __init__(self, expr):
        self.expr = expr


class Expression(BaseAst):
    pass


class Name(BaseAst):
    def __init__(self, name):
        self.name = name


class BinOp(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class Add(BinOp):
    pass


class Sub(BinOp):
    pass


class Mul(BinOp):
    pass


class Div(BinOp):
    pass


# ____________________________________________________________
# parser

pg = ParserGenerator(
    alltokens, precedence=[("left", ["PLUS", "MINUS"]), ("left", ["MUL", "DIV"])]
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


@pg.production("element : COMPUTE NAME EQUAL expression")
def compute_element(p):
    return Compute(p[1].value, p[3])


@pg.production("expression : NUMBER")
def expression_number(p):
    return Number(int(p[0].getstr()))


@pg.production("expression : NAME")
def expression_name(p):
    return Name(p[0].getstr())


@pg.production("expression : LPAREN expression RPAREN")
def expression_parens(p):
    return p[1]


@pg.production("expression : expression PLUS expression")
@pg.production("expression : expression MINUS expression")
@pg.production("expression : expression MUL expression")
@pg.production("expression : expression DIV expression")
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
    else:
        raise AssertionError("Oops, this should not be possible!")


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
    compute C = C1 + C2
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
    """
mul_pow2_const: int_mul(x, C)
    if C & (C - 1) == 0
    compute shift = highest_bit(C)
    => int_lshift(x, shift)

mul_lshift: int_mul(x, int_lshift(1, y))
    if intbound(y).known_ge_const(0) and intbound(y).known_le_const(LONG_BIT)
    => int_lshift(x, y)
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
    compute C = C1 + C2
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

    def emit(self, line=""):
        if self.level == 0 and line.startswith(("def ", "class ")):
            self.code.append("")
        if not line.strip():
            self.code.append("")
        else:
            self.code.append("    " * self.level + line)


def generate_code_pattern(p, varname, intbound_name, bindings):
    if isinstance(p, PatternVar):
        if p.name not in bindings:
            bindings[p.name] = varname
            return "True"
        else:
            return "%s is %s" % (varname, bindings[p.name])
    elif isinstance(p, PatternConst):
        return "%s.known_eq_const(%s)" % (intbound_name, p.const)
    import pdb

    pdb.set_trace()


def generate_target(target, bindings):
    if isinstance(target, PatternVar):
        return "self.make_equal_to(op, %s)" % bindings[target.name]
    if isinstance(target, PatternConst):
        return "self.make_constant_int(op, %s)" % target.const
    if isinstance(target, PatternOp):
        return
    import pdb

    pdb.set_trace()


def generate_code(ast):
    per_op = defaultdict(list)
    for rule in ast.rules:
        per_op[rule.pattern.opname].append(rule)
    res = []
    for opname, rules in per_op.items():
        res.append("def optimize_%s(self, op):" % opname.upper())
        numargs = len(rules[0].pattern.args)
        for i in range(numargs):
            res.append("    arg%s = get_box_replacement(op.getarg(%s))" % (i, i))
            res.append("    b%s = self.getintbound(arg%s)" % (i, i))
        for rule in rules:
            bindings = {}
            patterncomp = " and ".join(
                [
                    "(" + generate_code_pattern(p, "a%s" % i, "b%s" % i, bindings) + ")"
                    for i, p in enumerate(rule.pattern.args)
                ]
            )
            targetcomp = generate_target(rule.target, bindings)
            res.append("    if %s:" % patterncomp)
            res.append("        %s" % targetcomp)
            res.append("        return")
    import pdb

    pdb.set_trace()


def xtest_generate_code():
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
    s = generate_code(parse(s))


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
