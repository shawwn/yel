from __future__ import annotations

import re
import keyword as keywordlib
import json
import ast

from .constants import *

def compiled_prefix():
    return "LISP_"

def compile_char(c: str):
    if c == "-":
        return "_"
    if c.isdigit():
        return c
    return f'_0{ord(c):02o}'

def uncompile_char(c: str):
    if m := re.fullmatch("[_]([0][0-9][0-9]+)", c):
        it = m.groups()[0]
        code = int(it, 8)
        return chr(code)
    if c == "_":
        return "-"
    else:
        return c

def compile_id_rest(id: str, name: str):
    if not id.isidentifier():
        return ["_", id]
    if id.startswith("_") and not name.startswith("-"):
        return [compiled_prefix(), id]
    if keywordlib.iskeyword(id):
        return [id, "_"]

def compile_id(name: str):
    id = name
    if id.endswith("?"):
        id = id[:-1] + ("-p" if "-" in name else "p")
    id = ''.join([compile_char(c) if not (c.isalpha() or c == "-") or not c.isidentifier() else c for c in id])
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
            return compile(["%array"])
        x, *args = e
        if string(x) and x in forms:
            return forms[x](*args)
        return compile_call(x, *args)
    else:
        return compile_atom(e)

def compile(e):
    e = compile1(e)
    while sequence(e):
        e = compile1(e)
    return e

forms = globals().setdefault("forms", {})

def form(name):
    def setter(f):
        forms[name] = f
        return f
    return setter

@form("%atom")
def compile_atom(e):
    if string(e):
        if e.startswith("*"):
            return "*" + compile_atom(e[1:])
        if e == "/":
            return e
        if numeric_literal(e):
            return e
        # if e and (e.startswith("\"") or e[0].isdigit()) and escape(unescape(e)) == e:
        if string_literal(e):
            return e
        if string_literal(e, "|"):
            return e[1:-1]
        if e:
            e1 = compile_id(e)
            if not eq(e1, e):
                e1 = compile(["get", ["globals"], ["quote", e]])
            return e1
        return e
    return escape(e)

@form("%literal")
def compile_literal(*args):
    return mapcat(lambda x: compile(x) if eq(x, unescape(x)) else unescape(x), args)

@form("%array")
def compile_array(*args):
    return "[" + mapcat(compile, args, sep=", ") + "]"

@form("%object")
def compile_object(*args):
    kvs = []
    for k, v in py.zip(args[0::2], args[1::2]):
        kvs.append(compile(k) + ": " + compile(v))
    return "{" + mapcat(nil, kvs, sep=", ") + "}"

@form("%unpack")
def compile_unpack(x):
    return "*" + compile(x)

@form("%spread")
def compile_spread(x):
    return "**" + compile(x)

@form("%name")
def compile_name(name):
    return ["%literal", escape(name)]

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
                kws.append(["%infix", k, "=", v])
            else:
                kws.append(["%spread", ["%object", ["quote", k], v]])
            i += 2
        else:
            xs.append(args[i])
            i += 1
    return mapcat(compile, xs + kws, sep=", ")

@form("%call")
def compile_call(f, *args):
    if at(args, 0) == "for" and at(args, 2) == "in":
        return "(" + compile_infix(f, *args) + ")"
    return compile(f) + "(" + compile_args(args) + ")"

@form("get")
def compile_get(l, k):
    if accessor(k):
        if accessor_name(k).isidentifier():
            return compile(l) + k
        else:
            return ["get", [l, ".__dict__"], ["quote", accessor_name(k)]]
    return "(" + compile(l) + ")" + "[" + compile(k) + "]"

@form("set")
def compile_set(lh, rh):
    return compile(lh) + " = " + compile(rh)

@form("quote")
def compile_set(x):
    return escape(x)

@form("return")
def compile_return(x=unset):
    if x is unset:
        return "return"
    return "return " + compile(x)

@form("do")
def compile_do(*args):
    return mapcat(compile_statement, args)

@form("async")
def compile_async(*form):
    return "async " + compile(form)

@form("%parens")
def compile_parens(x):
    return cat("(", compile(x), ")")

@form("fn")
def compile_fn(args, body):
    return ["%parens", ["%literal", '"lambda "', ["%args", args], '": "', body]]

@form("def")
def compile_def(name, args, *body):
    return ["%block", "def", [["%name", name], *(args or ())], *body]

@form("class")
def compile_class(name, args, *body):
    return ["%block", "class", [["%name", name], *(args or ())], *body]

@form("with")
def compile_with(x, *body):
    if at(body, 0) == "as":
        name = body[1]
        body = body[2:]
        x = ["%infix", x, "as", name]
    return ["%block", "with", x, *body]

@form("after")
def compile_after(e, *body):
    return ["do",
            ["%block", "try", nil, e],
            ["%block", "finally", nil, ["do", *body]]]

@form("import")
def compile_import(lib, *args):
    form = ["%literal", '"import "', ["%name", lib]]
    if at(args, 0) == "as":
        alias = args[1]
        form.extend(['" as "', ["%name", alias]])
    return form

@form("from")
def compile_from(lib, _import, names, *args):
    assert _import == "import"
    return ["%literal", '"from "', escape(lib), '" "', ["import", names, *args]]

@form("for")
def compile_for(x, _in, l, *body):
    assert _in == "in"
    return ["%block", 'for', ["%infix", x, "in", l], ["do", *body]]

@form("%infix")
def compile_infix(x, *rest):
    s = compile(x)
    while rest:
        op, y, *rest = rest
        s += " " + op + " "
        s += compile(y)
    return s

@form("@")
def compile_decorator(x):
    return "@" + compile(x)

@form("%block")
def compile_block(name, x, *body):
    if x is nil:
        s = name + ":\n"
    else:
        s = name + " " + compile(x) + ":\n"
    return s + compile_body(*body)

def compile_body(*body):
    with indent("  "):
        return mapcat(compile_statement, body)

def compile_statement(x):
    return indentation() + compile(x).strip() + "\n"

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


