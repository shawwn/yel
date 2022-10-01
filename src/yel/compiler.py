from __future__ import annotations

import re
import keyword as keywordlib
import json
import ast

from .constants import *

def compiled_prefix():
    return "LISP_"

def compile_char(c: str):
    # if c == "-":
    #     return "_"
    if c.isdigit():
        return c
    return f'_0{ord(c):02o}'

def uncompile_char(c: str):
    if m := re.fullmatch("[_]([0][0-9][0-9]+)", c):
        it = m.groups()[0]
        code = int(it, 8)
        return chr(code)
    # if c == "_":
    #     return "-"
    return c

def compile_id_rest(id: str, name: str):
    if not id.isidentifier():
        return ["_", id]
    if id.startswith("_") and not name.startswith("_"):
        return [compiled_prefix(), id]
    if keywordlib.iskeyword(id):
        return [id, "_"]

def compile_id(name: str):
    id = name
    if id.endswith("?"):
        id = id[:-1] + ("_p" if "_" in name else "p")
    id = ''.join([compile_char(c) if not (c.isalpha() or c == "_") or not c.isidentifier() else c for c in id])
    if len(id) > 1:
        id = id.replace('-', '_')
    while it := compile_id_rest(id, name):
        id = ''.join(it)
    return id

def uncompile_id(id: str):
    if id.endswith("_p"):
        id = id[:-2] + "?"
    elif id.endswith("p"):
        id = id[:-1] + "?"
    if id.startswith(compiled_prefix()):
        id = id[len(compiled_prefix()):]
    def replace(m: re.Match):
        return uncompile_char(m.groups()[0])
    id = re.sub("([_](?:[0][0-9][0-9]+)?)", replace, id)
    return id

def escape(x):
    return json.dumps(x)

def unescape(x):
    try:
        return ast.literal_eval(x)
    except (ValueError, SyntaxError):
        return x

def method_call(form):
    if sequence(form) and accessor(car(form)):
        return t

def transform(e):
    if method_call(it := at(e, 1)):
        x = join(["get", car(e), car(it)], cdr(it))
    elif accessor(it := at(e, 1)) and at(e, 0) != "from": # a hack for (from . import foo)
        x = ["get", car(e), it]
    else:
        return e
    if it := cdr(cdr(e)):
        return transform(join(x, it))
    return x

def compile1(e):
    e = transform(e)
    if sequence(e):
        if len(e) <= 0:
            return ["%tuple"]
        x, *args = e
        if string(x) and x in forms:
            return forms[x](*args)
        return compile_call(x, *args)
    else:
        return compile_atom(e)

def compile(e):
    while sequence(e := compile1(e)):
        pass
    return e

forms = globals().setdefault("forms", {})

def form(*names):
    def setter(f):
        for name in names:
            forms[name] = f
        return f
    return setter

@form("%atom")
def compile_atom(e):
    if string(e):
        # if e.startswith("*"):
        #     return "*" + compile_atom(e[1:])
        # if e == "/":
        #     return e
        if numeric_literal(e):
            return e
        # if e and (e.startswith("\"") or e[0].isdigit()) and escape(unescape(e)) == e:
        if string_literal(e):
            return e
        if string_literal(e, "|"):
            return e[1:-1]
        if e:
            e1 = compile_id(e)
            # if not eq(e1, e):
            #     e1 = compile(["%get", ["globals"], ["quote", e]])
            #     # e1 = compile(["%get", ["globals"], escape(e) if string(e) else ["%quote", e]])
            return e1
        return e
    return escape(e)

@form("%snake")
def compile_snake(*args):
    # print(args)
    # print(compile(args))
    # print(compile_get(*args))
    # print(compile(["%literal", *args]))
    # return mapcat(lambda x: compile(x) if eq(x, unescape(x)) else unescape(x), args)
    # return ""
    return ["%literal", *args]

@form("%literal")
def compile_literal(*args):
    return mapcat(lambda x: compile(x) if eq(x, unescape(x)) else unescape(x), args)

@form("%array")
def compile_array(*args):
    return "[" + mapcat(compile, args, sep=", ") + "]"

@form("%object")
def compile_object(*args):
    if len(args) > 2 and args[1] == "for":
        x, *args = args
        k, v = x
        return "{" + compile_infix(["%colon", k, v], *args) + "}"
    if any([carp(x, "**") or carp(x, "%spread") for x in args]):
        return "{" + mapcat(compile, args, sep=", ") + "}"
    kvs = []
    for k, v in py.zip(args[0::2], args[1::2]):
        kvs.append(compile(k) + ": " + compile(v))
    return "{" + mapcat(nil, kvs, sep=", ") + "}"

@form("%colon")
def compile_colon(x, y):
    return compile(x) + ": " + compile(y)

@form("%unpack")
def compile_unpack(x):
    return "*" + compile(x)

@form("%spread")
def compile_spread(x):
    return "**" + compile(x)

@form("%name")
def compile_name(name):
    return ["%literal", escape(name)]

@form("%id")
def compile_name(name):
    return ["%literal", escape(compile_id(name))]

@form("%args")
def compile_args(args):
    xs = []
    kws = []
    i = 0
    while i < len(args):
        if keyword(args[i]):
            k = keyword_name(args[i])
            v = args[i + 1]
            if compile_id(k) == k:
                kws.append(["%set", k, v])
            else:
                kws.append(["%spread", ["%object", ["%quote", k], v]])
            i += 2
        else:
            xs.append(args[i])
            i += 1
    return mapcat(compile_arg, xs + kws, sep=", ")

def compile_arg(x):
    if string(x):
        if x.startswith("*"):
            return "*" + compile_arg(x[1:])
        if x == "/":
            return x
    return compile(x)

@form("%call")
def compile_call(f, *args):
    if at(args, 0) == "for" and at(args, 2) == "in":
        return "(" + compile_infix(f, *args) + ")"
    return compile(f) + "(" + compile_args(args) + ")"

@form("%brackets")
def compile_brackets(*body):
    return ["%array", *body]

@form("%braces")
def compile_braces(*body):
    return ["%object", *body]

@form("%tuple", ",")
def compile_tuple(*args, parens=True):
    e = mapcat(compile, args, sep=", ")
    if len(args) == 1:
        e += ","
    return ["%parens", e] if parens else e
    # if args[1:]:
    #     return mapcat(compile, args, sep=", ")
    # elif args:
    #     return ", " + compile(args[0])
    # else:
    #     return ", "

# (define infix
#   `((%not: (js: ! lua: not py: not) %neg: -)
#     (%mul: * %div: / %idiv: // %mod: %)
#     (%cat: (js: + lua: .. py: +))
#     (%add: + %sub: -)
#     (%lt: < %gt: > %le: <= %ge: >=)
#     (%eq: (js: === lua: == py: ==))
#     (%in: (py: in) %is: (py: is))
#     (%and: (js: && lua: and py: and))
#     (%or: (js: ,"||" lua: or py: or))))
# infix = [x.split() for x in """
# %not %neg
# %mul %div %mod
# %cat
# %add %sub
# %lt %gt %le %ge
# %eq
# %in %is
# %and
# %or
# """.strip().splitlines()]

infix = [
    # {"%get": lambda l, k: compile_get(l, k)},
    {"%await":  "await"},
    {"%pow":  "**"},
    {"%pos": "+", "%neg": "-", "%bnot": "~"},
    {"%mul": "*", "%matmul": "@", "%div": "/", "%idiv": "//", "%mod": "%"},
    {"%cat": "+"},
    {"%add": "+", "%sub": "-"},
    {"%lsh": "<<", "%rsh": ">>"},
    {"%band": "&"},
    {"%bxor": "^"},
    {"%bor": "|"},
    {"%lt": "<", "%gt": ">", "%le": "<=", "%ge": ">="},
    {"%eq": "==", "%ne": "!="},
    {"%in": "in", "%is": "is"},
    {"%not": "not"},
    {"%and": "and"},
    {"%or": "or"},
    ]

unary = ["%pos", "%neg", "%bnot", "%not"]

# (define unary? (form)
#   (and (two? form) (in? (hd form) '(%not %neg))))
def unaryp(form):
    return sequence(form) and len(form) == 2 and string(car(form)) and car(form) in unary

def formop(op, *alias):
    @form(op, *alias)
    def compile_it(*args, **kws):
        return compile_op(op, *args, **kws)
    compile_it.__name__ = "compile_" + op
    return compile_it

for frame in infix:
    for k, v in frame.items():
        globals()["compile_" + k.lstrip("%")] = formop(k, v)

# @form("%neg")
# def compile_neg(x):
#     return compile_op("%neg", x)
#
# @form("%pos")
# def compile_pos(x):
#     return compile_op("%pos", x)

@form("-")
def compile_minus(*args):
    if len(args) > 1:
        return ["%sub", *args]
    elif args:
        return ["%neg", *args]
    else:
        return ["%do"]

@form("+")
def compile_plus(*args):
    if len(args) > 1:
        return ["%add", *args]
    elif args:
        return ["%pos", *args]
    else:
        return ["%do"]

@form("*")
def compile_star(*args):
    if len(args) > 1:
        return ["%mul", *args]
    elif args:
        return ["%unpack", *args]
    else:
        return ["%do"]


@form("**")
def compile_starstar(*args):
    if len(args) > 1:
        return ["%pow", *args]
    elif args:
        return ["%spread", *args]
    else:
        return ["%do"]

# (define index (k)
#   (target k lua: (when (number? k) (- k 1))))
#
# (define precedence (form)
#   (unless (or (atom? form) (unary? form))
#     (when (atom? (hd form))
#       (each (k v) infix
#         (if (has? v (hd form)) (return (index k))))))
#   0)
def precedence(form):
    # if not (not sequence(form) or unaryp(form)):
    if sequence(form):
        op = car(form)
        if not sequence(op):
            for i, v in py.enumerate(infix):
                if op in v:
                    return i
            for i, entry in py.enumerate(infix):
                for k, v in entry.items():
                    if v == op:
                        if k in unary and len(form) == 2:
                            return i
                        elif k not in unary and len(form) > 2:
                            return i
    return 0

# (define getop (op)
#   (when (string? op)
#     (find (fn (level)
#             (let x (has level op)
#               (if (= x true) op
#                   (string? x) x
#                   (is? x) (has x target))))
#           infix)))
def getop(op):
    if string(op):
        for level in infix:
            if op in level:
                x = level[op]
                if x is True:
                    return op
                # if string(x):
                #     return x
                # if x:
                #     return x
                if string(x):
                    return x

# (define infix? (x)
#   (is? (getop x)))
def infixp(x):
    return getop(x)

# (define-global infix-operator? (x)
#   (and (not (atom? x)) (infix? (hd x))))
def infix_operator_p(x):
    return sequence(x) and infixp(car(x))

# (define op-delims (parent child right: right)
#   (if ((if right >= >)
#        (precedence child)
#        (precedence parent))
#       (list "(" ")")
#     (list "" "")))
def op_delims(parent, child, right=False):
    a, b = precedence(child), precedence(parent)
    if (a >= b) if right else (a > b):
        return "(", ")"
    else:
        return "", ""

def op_parens(parent, child, right=False):
    a, b = precedence(child), precedence(parent)
    if (a >= b) if right else (a > b):
        return t
    else:
        return nil


# (define compile-infix (form)
#   (let ((op rest: (a b)) form
#         (ao ac) (op-delims form a)
#         (bo bc) (op-delims form b right: true)
#         a (compile a)
#         b (compile b)
#         op (getop op))
#     (if (unary? form)
#         (cat op ao " " a ac)
#       (cat ao a ac " " op " " bo b bc))))
def compile_binary(op, a, b):
    form = [op, a, b]
    ao, ac = op_delims(form, a)
    bo, bc = op_delims(form, b, right=True)
    # a = compile(a)
    # b = compile(b)
    if unaryp(form):
        return (op, ao, " ", a, ac)
    else:
        return (ao, a, ac, " ", op, " ", bo, b, bc)

def compile_unary(op, x, parens=False):
    if parens:
        x = ["%parens", x]
    return ["%prefix", op, x]

def compile_op(op, a, *args, parens=unset):
    form = [op, a]
    op = getop(op) or op
    ao = op_parens(form, a)
    if ao:
        a = ["%parens", a]
    if unaryp(form):
        # ao, ac = op_delims(form, a)
        # if ao:
        #     a = ["%parens", a]
        return ["%prefix", op, a]
    elif args:
        b, *args = args
        form = [op, a, b]
        # if not args:
        bo = op_parens(form, b, t)
        # ao, ac = op_delims(form, a)
        # bo, bc = op_delims(form, b, t)
        # if ao:
        #     a = ["%parens", a]
        # if bo:
        #     b = ["%parens", b]
        # if unaryp(form):
        #     return ["%prefix", op, a]
        bs = compile_op(op, b, *args) if args else b
        if bo:
            bs = ["%parens", bs]
        return ["%infix", a, op, bs]
        # return ["%parens", e] if parens else e
    return a

# @form("%or", "or")
# def compile_or(x, *args):
#     return compile_op("%or", x, *args)
#
# @form("%and", "and")
# def compile_and(x, *args):
#     return compile_op("%and", x, *args)
#
# @form("%not", "not")
# def compile_not(x):
#     # return ["%literal", '"not "', ["%parens", x]]
#     return compile_op("%not", x)

@form("%eq", "=")
def compile_eq(x, *args):
    return compile_op("%eq", x, *args)

# @form("%le", "<=")
# def compile_le(x, *args):
#     return compile_op("%le", x, *args)
#
# @form("%lt", "<")
# def compile_lt(x, *args):
#     return compile_op("%lt", x, *args)
#
# @form("%ge", ">=")
# def compile_ge(x, *args):
#     return compile_op("%ge", x, *args)
#
# @form("%gt", ">")
# def compile_gt(x, *args):
#     return compile_op("%gt", x, *args)
#
# @form("%in", "in")
# def compile_in(x, y):
#     return compile_op("%in", x, y)
#
# @form("%is", "is")
# def compile_is(x, y):
#     return compile_op("%is", x, y)

@form("%if", "if")
def compile_if(cond, cons, else_=unset):
    e = ["%block", "if", cond, cons]
    if else_ is unset:
        return e
    return ["%do", e, ["%block", "else", nil, else_]]

@form("%get", "get")
def compile_get(l, k, *ks):
    if accessor(k):
        if accessor_name(k).isidentifier() or ks or t:
            return compile(l) + mapcat(nil, [k, *ks])
        else:
            return ["%get", [l, ".__dict__"], escape(accessor_name(k))]
    else:
        # if accessor(k):
        #     return compile(l) + mapcat(nil, [k, *ks])
        # return compile(l) + "[" + mapcat(compile, [k, *ks], sep=", ") + "]"
        return compile(l) + "[" + mapcat(compile, [k, *ks], sep=", ") + "]"

@form("%set", "set")
def compile_set(lh, rh):
    return compile(lh) + " = " + compile(rh)

@form("%quote", "quote")
def compile_set(x):
    return escape(x)

@form("%return", "return")
def compile_return(x=unset):
    if x is unset:
        return "return"
    return "return " + compile(x)

@form("%do", "do")
def compile_do(*args):
    return mapcat(compile_statement, args)

@form("%async", "async")
def compile_async(*form):
    return "async " + compile(form)

@form("%parens")
def compile_parens(x):
    return cat("(", x if string(x) else compile(x), ")")

@form("%function", "fn")
def compile_fn(args, body):
    return ["%parens", ["%literal", '"lambda "', ["%args", args], '": "', body]]

def compile_definition(form, name, args, *body, result=nil):
    if body and body[0] == "->":
        v = at(body, 1)
        if result is nil:
            result = v
        body = body[2:]
    if not args and form == "class":
        e = ["%id", name]
    else:
        e = [["%id", name], *(args or ())]
    if result:
        e = ["%literal", e, "| -> |", result]
    e = ["%block", form, e, *body]
    if compile_id(name) == name:
        return e
    return ["do", e, ["%set", name, ["%id", name]]]

@form("%define", "def")
def compile_def(name, args, *body, result=nil):
    return compile_definition("def", name, args, *body, result=result)

@form("%class", "class")
def compile_class(name, args, *body):
    return compile_definition("class", name, args or nil, *body)
#
# @form("%class", "class")
# def compile_class(name, args, *body):
#     return ["%block", "class", [name, *(args or ())], *body]

@form("%as", "as")
def compile_as(var, name):
    return ["%infix", var, "as", name]

@form("%with", "with")
def compile_with(x, *body):
    # if at(body, 0) == "as":
    #     name = body[1]
    #     body = body[2:]
    #     x = ["%as", x, name]
    return ["%block", "with", x, *body]

@form("%after", "after")
def compile_after(e, *body):
    # return ["do",
    #         ["%block", "try", nil, e],
    #         ["%block", "finally", nil, ["do", *body]]]
    return ["%blocks",
            ["try", nil, e],
            # ["except", ["%as", "Exception", "e"], ["print", "e"]],
            # ["except", ["%tuple", "ValueError", "KeyError"], "as", "e", ["print", "e"], ["raise", "e"]],
            # ["except", ["%as", "Exception" "e"], ["print", "e"], ["raise", "e"]],
            # ["else", nil, ["print", '"else"'], ["print", 42]],
            ["finally", nil, *body]]

@form("%import", "import")
def compile_import(lib, *args):
    # form = ["%literal", '"import "', ["%name", lib]]
    # if at(args, 0) == "as":
    #     alias = args[1]
    #     form.extend(['" as "', ["%name", alias]])
    # return form
    name = ["%name", lib]
    if at(args, 0) == "as":
        alias = args[1]
        name = ["%as", name, alias]
    return ["%prefix", "import", name]

@form("%from", "from")
def compile_from(lib, _import, names, *args):
    assert _import == "import"
    # return ["%literal", '"from "', escape(lib), '" "', ["import", names, *args]]
    return ["%prefix", "from", ["%name", lib], ["import", names, *args]]

@form("%for", "for")
def compile_for(x, _in, l, *body):
    assert _in == "in"
    # return ["%block", 'for', ["%infix", x, "in", l], ["do", *body]]
    return ["%block", 'for', ["%in", x, l], *body]

@form("%infix")
def compile_infix(x, *rest):
    s = compile(x)
    while rest:
        op, y, *rest = rest
        s += " " + op + " "
        s += compile(y)
    return s

@form("%prefix")
def compile_prefix(op, *body):
    return cat(op, " ", mapcat(compile, body, sep=" "))

@form("%decorator", "@")
def compile_decorator(x):
    return "@" + compile(x)

@form("%block")
def compile_block(name, x, *body):
    if x and at(body, 0) == "as":
        return compile_block(name, ["%as", x, body[1]], *body[2:])
    if x is nil:
        s = name + ":\n"
    else:
        s = name + " " + compile(x) + ":\n"
    return s + compile_body(*body)

@form("%blocks")
def compile_blocks(*clauses):
    return ["%do", *[["%block", *clause] for clause in clauses]]

@form("%body")
def compile_body(*body):
    with indent("    "):
        return mapcat(compile_statement, body or ["|pass|"])

@form("%stmt")
def compile_statement(x):
    ind = indentation()
    tr = "\n\n" if ind == "" else "\n"
    return ind + compile(x).strip() + tr

indentation_: CV.ContextVar[str] = globals().setdefault("indentation_", CV.ContextVar(__name__ + ".indentation", default=""))

def indentation(x=unset):
    if x is unset:
        return indentation_.get()
    else:
        indentation_.set(x)

def with_indentation(x: str):
    return CV_let(indentation_, x)

def indent(by: str = "  "):
    return with_indentation(indentation() + by)


@form("%when", "when")
def compile_when(cond, *body):
    return ["%if", cond, ["%do", *body]]

@form("%unless", "unless")
def compile_unless(cond, *body):
    return ["%if", ["%not", cond], ["%do", *body]]

