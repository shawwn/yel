from __future__ import annotations
from typing import *
import collections.abc as std
import builtins as py
import contextlib
import itertools
import functools
import ast
import inspect
import types
import os
from importlib import reload

from .constants import *
from . import reader
from . import compiler
from . import util

import sys
M = sys.modules[__name__]

def apply(f, args=nil, kws: Mapping = nil):
    return f(*(args or ()), **(kws or {}))

def cadr(x):
    return car(cdr(x))

def cddr(x):
    return cdr(cdr(x))

def caddr(x):
    return car(cddr(x))

def null(x):
    if x is nil:
        return t

def ok(x):
    if not null(x):
        return t

def no(x):
    if not x:
        return t

def yes(x):
    if not no(x):
        return t

def idfn(x):
    return x

def map(f, *args):
    return py.list(py.map(f, *(l or () for l in args)))

def mapcat(f, *args, sep=""):
    r = []
    for x in map(f or idfn, *args):
        if ok(x):
            r.append(py.str(x))
    return sep.join(r)

def reduce(f, xs):
    a, bs = car(xs), cdr(xs)
    return f(a, reduce(f, bs)) if bs else a

def append(*ls):
    r = Seq()
    for l in ls:
        if l:
            r.extend(l)
    return r

def cons(*args):
    return reduce(join, args)

assert cons(1, [2, 3, 4]) == [1, 2, 3, 4]
assert cons(1, 2, 3, [4]) == [1, 2, 3, 4]

def snoc(*args):
    return append(car(args), cdr(args))

assert snoc([4, 3, 2], 1) == [4, 3, 2, 1]
assert snoc([4], 3, 2, 1) == [4, 3, 2, 1]

def list(*args):
    # return append(args, nil)
    return Seq(args)

# def map(f, *args):
#     if some(null, args):
#         return nil
#     return py.map(f, *(arg for arg in args if arg))

def some(f, xs):
    for x in xs or ():
        if f(x):
            return xs

def all(f, xs):
    for x in xs or ():
        if not f(x):
            return nil
    return t

def pair(x):
    if x and sequence(x):
        return t

assert not pair(())
assert not pair([])
assert pair((1,))
assert pair((1,))
assert pair(join())
assert not pair({})
assert not pair(1)
assert not pair(nil)
assert not pair(t)
assert not pair(False)
assert not pair("x")

def atom(x):
    if not pair(x):
        return t

assert atom(())
assert atom([])
assert not atom((1,))
assert not atom([1])
assert not atom(join())
assert atom({})
assert atom(1)
assert atom(nil)
assert atom(t)
assert atom(False)
assert atom("x")

def equal(*args):
    """
    (def = args
      (if (no (cdr args))  t
          (some atom args) (all [id _ (car args)] (cdr args))
                           (and (apply = (map car args))
                                (apply = (map cdr args)))))
    """
    if some(atom, args):
        y, xs = car(args), cdr(args)
        if all(lambda x: eq(x, y), xs):
            return t
    else:
        if equal(*map(car, args)) and equal(*map(cdr, args)):
            return t
    # for lh, rh in itertools.pairwise(args):
    #     if not (lh == rh):
    #         return nil
    # return t

assert equal([1, 2], (1, 2), [1, 2])
assert not equal([1, 2], (1, 2), [1, 2], 3)
# assert equal([], nil, False)

def mem(x, ys, f=equal):
    """
    (def mem (x ys (o f =))
      (some [f _ x] ys))
    """
    # return some(lambda y: f(y, x), ys)
    return py.any(f(y, x) for y in ys or ())

def begins(xs, pat, f=equal):
    """
    (def begins (xs pat (o f =))
      (if (no pat)               t
          (atom xs)              nil
          (f (car xs) (car pat)) (begins (cdr xs) (cdr pat) f)
                                 nil))
    """
    if no(pat):
        return t
    if atom(xs):
        return nil
    if f(car(xs), car(pat)):
        return begins(cdr(xs), cdr(pat), f)
    return nil

def caris(x, y, f=equal):
    """
    (def caris (x y (o f =))
      (begins x (list y) f))
    """
    return begins(x, [y], f)

def keep(f, xs):
    """
    (def keep (f xs)
      (if (no xs)      nil
          (f (car xs)) (cons (car xs) (keep f (cdr xs)))
                       (keep f (cdr xs))))
    """
    return append(x for x in xs or () if f(x))

def bel(e, g: List[Dict] = unset, a: List[MutableMapping] = unset, p: List[Tuple[List, Dict]] = unset):
    """
    (def bel (e (o g globe))
      (ev (list (list e nil))
          nil
          (list nil g)))
    """
    g = [init(g, lambda: [globals(), py.__dict__])]
    a = [init(a, lambda: [])]
    p = init(p, lambda: [])
    return tev(ev,
               [[e, a]],
               [],
               [p, g])

def tev(f, s: List[List], r: List, m: Tuple[List, Dict]):
    while True:
        it = f(s, r, m)
        if f == fin:
            return it
        f, (s, r, m) = it

def fin(s, r, m):
    assert len(r) == 1
    return car(r)

def mev(s: List[List], r: List, m: Union[Tuple[List, Dict], List[List]]):
    """
    (def mev (s r (p g))
      (if (no s)
          (if p
              (sched p g)
              (car r))
          (sched (if (cdr (binding 'lock s))
                     (cons (list s r) p)
                     (snoc p (list s r)))
                 g)))
    """
    p, g = m
    if no(s):
        if p:
            return sched(p, g)
        else:
            return fin, (s, r, m)
    else:
        return sched(if_(yes(binding("lock", s)),
                         lambda: cons([s, r], p),
                         lambda: snoc(p, [s, r]))(),
                     g)

def sched(p: List, g: Dict):
    """
    (def sched (((s r) . p) g)
      (ev s r (list p g)))
    """
    (s, r), p = car(p), cdr(p)
    return ev, (s, r, (p, g))

def ev(s: List[List], r: List, m: Tuple[List, Dict]):
    """
    (def ev (((e a) . s) r m)
      (aif (literal e)            (mev s (cons e r) m)
           (variable e)           (vref e a s r m)
           (no (proper e))        (sigerr 'malformed s r m)
           (get (car e) forms id) ((cdr it) (cdr e) a s r m)
                                  (evcall e a s r m)))
    """
    [e, a], s = car(s), cdr(s)
    if literal(e):
        return evliteral(e, a, s, r, m)
    if variable(e):
        return vref(e, a, s, r, m)
    e = transform(e)
    # print()
    # print("> ", e, dict(s=s, r=r, a=a))
    if not unset(it := get(forms, car(e), eq)):
        return it(cdr(e), a, s, r, m)
    if callable(car(e)):
        return evcall2(cdr(e), a, s, cons(car(e), r), m)
    return evcall(e, a, s, r, m)

def method_call(form):
    if pair(form) and accessor(car(form)):
        return t

def transform(e):
    if method_call(it := cadr(e)):
        x = cons(list("grab", car(e), car(it)), cdr(it))
    elif accessor(cadr(e)):
        x = list("grab", car(e), cadr(e))
    else:
        return e
    if cddr(e):
        return transform(cons(x, cddr(e)))
    return x

class Bindings(py.dict):
    def __init__(self, a, s, r, m, scope=t, globe=t, bindings=t):
        super().__init__()
        self.frame = [a, s, r, m]
        self._scope = scope
        self._globe = globe
        self._bindings = bindings

    def copy(self):
        return type(self)(*self.frame, scope=self._scope, globe=self._globe, bindings=self._bindings)

    @property
    def scope(self):
        if self._scope:
            a, s, r, m = self.frame
            return a
    @property
    def globe(self):
        if self._globe:
            a, s, r, m = self.frame
            p, g = car(m), cadr(m)
            return g
    @property
    def stack(self):
        if self._bindings:
            a, s, r, m = self.frame
            return s
    def bindings(self, stack=unset) -> List[std.Mapping]:
        if stack is unset:
            stack = self.stack
        l = {car(cell): cadr(cell) for cell in bindings(stack)}
        return [l] if l else []
    def locals(self, a=unset, acc=unset, setting=nil) -> List[std.Mapping]:
        if a is unset:
            a = self.scope
        if acc is unset:
            acc = []
        if sequence(a):
            for x in a:
                self.locals(x, acc, setting=setting)
        elif isinstance(a, std.Mapping):
            if setting and a in [M.__dict__, py.__dict__]:
                pass
            else:
                acc.append(a)
        return acc
    def globals(self, a=unset, acc=unset, setting=nil) -> List[std.Mapping]:
        return self.locals(self.globe, acc, setting=setting)
    def frames(self, setting=nil) -> List[std.Mapping]:
        if setting:
            return self.globals(setting=setting) + self.locals(setting=setting)
        else:
            return [dict(scope=self.scope, globe=self.globe)] + self.globals() + self.locals() + self.bindings()
    def seq(self, setting=nil):
        l = {}
        for kvs in reversed(self.frames(setting=setting)):
            for k, v in kvs.items():
                if not unset(v):
                    l[k] = v
            # l.update(kvs)
        return l
    def keys(self):
        return py.list(self.seq().keys())
    def values(self):
        return py.list(self.seq().values())
    def items(self):
        return py.list(self.seq().items())
    def __len__(self):
        return py.len(self.seq())
    def __iter__(self):
        return py.iter(self.seq())
    def __repr__(self):
        l = self.seq()
        if l.get("__builtins__") is py:
            l.pop("__builtins__")
        return py.repr(l)

    def get(self, key, *default):
        try:
            return self[key]
        except KeyError:
            if default:
                return default[0]
            else:
                return nil

    def pop(self, __key: KT) -> VT:
        raise NotImplementedError("pop")

    def popitem(self) -> tuple[KT, VT]:
        raise NotImplementedError("popitem")

    def setdefault(self, __key: KT, __default: VT = ...) -> VT:
        raise NotImplementedError("setdefault")

    def update(self, __m: Mapping[KT, VT], **kwargs: VT) -> None:
        raise NotImplementedError("update")

    def clear(self) -> None:
        raise NotImplementedError("clear")

    def __contains__(self, item):
        try:
            self[item]
            return True
        except KeyError:
            return False

    def __getitem__(self, e):
        # print("Bindings.__getitem__", e)
        if not unset(it := lookup(e, *self.frame)):
            return it
        if eq(e, "unset"):
            return unset
        raise KeyError(e)
    # def __getattr__(self, item):
    #     try:
    #         return self[item]
    #     except KeyError:
    #         raise AttributeError(item)
    def __setitem__(self, e, v):
        print("Bindings.__setitem__", e, v)
        if not unset(it := lookup(e, *self.frame, setter=t)):
            return it(v)
        if not unset(g := lookup("scope", *self.frame)):
            while sequence(g):
                g = at(g, -1)
            if isinstance(g, std.MutableMapping):
                g[e] = v
                return
        raise KeyError(e)
    # def __setattr__(self, e, v):
    #     try:
    #         self[e] = v
    #     except KeyError:
    #         raise AttributeError(e)
    def __hash__(self):
        return hash(py.id(self))

def getenv(a, s, r, m):
    p, g = car(m), cadr(m)
    locals_ = Bindings(a, s, r, [p, [a, g]])
    globals_ = Bindings(nil, s, r, [p, [a, g]])
    return globals_, locals_

def evcode(code, a, s, r, m, *, filename="<unknown>", flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT):
    try:
        co = py.compile(code, filename, "eval", flags=flags)
        ex = py.eval
    except SyntaxError:
        co = py.compile(code, filename, "exec", flags=flags)
        ex = py.exec
    globals_, locals_ = getenv(a, s, r, m)
    e = ex(co, globals_, locals_)
    return e

def evliteral(e, a, s, r, m):
    def evlit(e):
        if id_literal(e):
            code = e[1:-1] if string(e) else mapcat(evlit, cdr(e))
            e = evcode(code, a, s, r, m)
            # try:
            #     co = py.compile(code, "<unknown>", "eval")
            #     ex = py.eval
            # except SyntaxError:
            #     co = py.compile(code, "<unknown>", "exec")
            #     ex = py.exec
            # # globals_ = Bindings(nil, s, r, m)
            # # locals_ = Bindings(a, nil, nil, [car(m), nil])
            # globals_, locals_ = getenv(a, s, r, m)
            # e = ex(code, globals_, locals_)
            # # try:
            # #     g = py.dict(__builtins__=env)
            # #     e = ex(code, g, env)
            # # except SystemError:
            # #     g = py.dict(__builtins__=py.dict(__import__=py.__import__))
            # #     e = ex(code, g, env)
        elif string_literal(e) or numeric_literal(e):
            e = ast.literal_eval(e)
        return e
    e = evlit(e)
    # print("evliteral", e)
    return mev(s, cons(e, r), m)

class Macro(Seq):
    def __init__(self, f):
        super().__init__(["lit", "mac", f])
    def __call__(self, *args, **kwargs):
        return caddr(self)(*args, **kwargs)

def bind(lh, rh, *body, **kws):
    if no(lh):
        return [["do", *body]]
    # if keyword(lh):
    #     k = keyword_name(lh)
    #     return ["let", kws.pop(k),
    if atom(lh):
        return [["let", lh, rh, *body]]
    rest = bind(cdr(lh), cdr(rh), *body, **kws)
    return bind(car(lh), car(rh), *rest, **kws)

def proper(x):
    if no(x):
        return t
    if pair(x):
        if not (len(x) >= 3 and x[-2] == "."):
            return t
    return nil

def mkproper(l, tail=snoc):
    if proper(l):
        return l
    elif pair(l):
        return tail(l[:-2], l[-1])
    else:
        return tail([], l)

def mkparms(x):
    if atom(x):
        return x




class Function(Seq):
    def __init__(self, scope, globe, parms, body):
        super().__init__(["lit", "clo", [scope, globe], parms, body])

    @property
    def env(self):
        return self[2]

    @property
    def parms(self):
        return self[3]

    @property
    def body(self):
        return self[4]

    def compile(self):
        inits = []
        rest = []
        names = {}
        def compile_arg(x):
            if caris(x, "o"):
                name = cadr(x)
                form = caddr(x) or "nil"
                inits.append([name, form])
                return compile_arg(name) + "=unset"
            if string(x):
                if x.startswith("*"):
                    return "*" + (compile_arg(x[1:]) or "")
                if x == "/":
                    return x
            if x:
                v = compiler.compile_id(x)
                names[v] = x
                return v
        return "lambda " + mapcat(compile_arg, self.parms, sep=", ") + ": locals()"

    @property
    @functools.lru_cache(maxsize=None)
    def func(self):
        return py.eval(self.compile(), {}, {})

    @property
    def __signature__(self):
        return inspect.signature(self.func)

    def bind(self, args, kws):
        return self.func(*(args or ()), **(kws or {}))

    def __call__(self, *args, **kwargs):
        scope, globe = self.env
        scope = cons(self.bind(args, kwargs), scope)
        return bel(self.body, globe, scope)

    def __repr__(self):
        rest = cddr(self)
        scope, globe = car(rest)
        return repr(list("lit", "clo", scope, self.parms, self.body))

@Macro
def when(x, *body):
    return ["if", x, ["do", *body]]

@Macro
def fn(parms, *body):
    return ["Function", "scope", "globe", ["quote", parms], ["quote", ["do", *body]]]

def vref(v, a, s, r, m):
    """
    (def vref (v a s r m)
      (let g (cadr m)
        (if (inwhere s)
            (aif (or (lookup v a s g)
                     (and (car (inwhere s))
                          (let cell (cons v nil)
                            (xdr g (cons cell (cdr g)))
                            cell)))
                 (mev (cdr s) (cons (list it 'd) r) m)
                 (sigerr 'unbound s r m))
            (aif (lookup v a s g)
                 (mev s (cons (cdr it) r) m)
                 (sigerr (list 'unboundb v) s r m)))))
    """
    if not unset(it := lookup(v, a, s, r, m)):
        return mev(s, cons(it, r), m)
    elif eq(v, "unset"):
        return mev(s, cons(unset, r), m)
    else:
        return sigerr(list("unboundb", v), s, r, m)

def lookup(e, a, s, r, m, *, setter=nil):
    """
    (def lookup (e a s g)
      (or (binding e s)
          (get e a id)
          (get e g id)
          (case e
            scope (cons e a)
            globe (cons e g))))
    """
    if not unset(it := binding(e, s, setter=setter)):
        return it
    if not unset(it := get(a, e, eq, setter=setter)):
        return it
    g = cadr(m)
    if not unset(it := get(g, e, eq, setter=setter)):
        return it
    if not setter:
        if eq(e, "scope"):
            return a
        if eq(e, "globe"):
            return g
        if eq(e, "frame"):
            return list(s, r, m)
    return unset

def binding(v, s, *, setter=nil):
    """
    (def binding (v s)
      (get v
           (map caddr (keep [begins _ (list smark 'bind) id]
                            (map car s)))
           id))
    """
    # if s:
    #     pat = [smark, "bind"]
    #     for [e, a] in s[-1:]:
    #         if begins(e, pat, eq):
    #             for [e, a] in s[:-1]:
    #                 if begins(e, pat, eq):
    #                     cell = caddr(e)
    #                     if caris(cell, v):
    #                         if setter:
    #                             return lambda v: operator.setitem(cell, 1, v)
    #                         return cadr(cell)
    # return unset
    for cell in bindings(s):
        if not unset(it := get(cell, v, eq, setter=setter)):
            return it
    return unset


def bindings(s) -> Generator[Dict]:
    if s:
        pat = [smark, "bind"]
        for [e, a] in s[-1:]:
            if begins(e, pat, eq):
                for [e, a] in s[:-1]:
                    if begins(e, pat, eq):
                        cell = caddr(e)
                        yield cell
                        # if caris(cell, v):
                        #     if setter:
                        #         return lambda v: operator.setitem(cell, 1, v)
                        #     return cadr(cell)

def sigerr(msg, s, r, m):
    """
    (def sigerr (msg s r m)
      (aif (binding 'err s)
           (applyf (cdr it) (list msg) nil s r m)
           (err 'no-err)))
    """
    raise ValueError(msg, s, r)

def id_literal(e):
    if string_literal(e, "|") or caris(e, "%literal"):
        return t

def literal(e):
    """
    (def literal (e)
      (or (in e t nil o apply)
          (in (type e) 'char 'stream)
          (caris e 'lit)
          (string e)))
    """
    if e in [t, nil, False, apply, unset]:
        return t
    # elif in_(type(e), quote("char"), quote("stream")):
    #     return t
    elif caris(e, "lit"):
        return t
    elif number(e):
        return t
    elif numeric_literal(e):
        return t
    elif string_literal(e):
        return t
    elif id_literal(e):
        return t
    elif accessor(e):
        return t
    elif keyword(e):
        return t
    elif sequence(e):
        if no(e):
            return t
        return nil
    elif callable(e):
        return t
    # else:
    #     return string(e)

assert literal(1)
assert literal(lambda: 42)
assert not literal("foo")
assert literal('"foo"')
assert literal("|foo|")
assert literal(list("lit"))
assert literal(["lit"])
assert not literal(["do", 1])

"""
(mac fn (parms . body)
  (if (no (cdr body))
      `(list 'lit 'clo scope ',parms ',(car body))
      `(list 'lit 'clo scope ',parms '(do ,@body))))
"""

"""
(set vmark (join))
"""
vmark = globals().setdefault("vmark", join("%vmark"))

class UVar(Seq):
    def __init__(self, name=unset):
        name = init(name, lambda: "v")
        super().__init__(list(vmark, name))
    def __repr__(self):
        return "#" + py.str(cadr(self))
    def __str__(self):
        return py.str(cadr(self)) + py.str(py.id(self))

def uvar(*info):
    """
    (def uvar ()
      (list vmark))
    """
    # return list(vmark, *info)
    return UVar(*(info or ["v"]))

"""
(def variable (e)
  (if (atom e)
      (no (literal e))
      (id (car e) vmark)))
"""
def variable(e):
    if atom(e):
        if no(literal(e)):
            return t
    else:
        if eq(car(e), vmark):
            return t

assert variable(uvar("a"))
assert variable("a")
assert not variable(1)
assert not variable(lambda: 42)
assert not variable(["do"])

def grab(x, *ks, error=True, setter=nil):
    self = x
    for k in (ks[:-1] if setter else ks):
        if accessor(k):
            it = accessor_name(k)
            if error:
                self = getattr(self, it)
            else:
                self = getattr(self, it, unset)
        elif number(k) or isinstance(k, py.slice):
            if error:
                self = operator.getitem(self, k)
            else:
                try:
                    self = operator.getitem(self, k)
                except IndexError:
                    self = unset
        if unset(self):
            break
    if unset(self) and error:
        raise KeyError(cons("grab", x, ks))
    if setter:
        lambda v: xset(self, ks[-1], v)
    return self

def xset(kvs, k, v):
    if accessor(k):
        it = accessor_name(k)
        if unset(v):
            try:
                delattr(kvs, it)
            except AttributeError:
                pass
        else:
            setattr(kvs, it, v)
    else:
        if unset(v):
            try:
                del kvs[k]
            except LookupError:
                pass
        else:
            kvs[k] = v

@dispatch
def get(kvs, k, test=equal, setter=nil):
    return grab(kvs, k, setter=setter)

@get.register(type(None))
def get_nil(kvs: None, k, test=equal, setter=nil):
    return unset

@get.register(std.Mapping)
def get_Mapping(kvs: Mapping, k, test=eq, setter=nil):
    if accessor(k):
        return grab(kvs, k, setter=setter)
    if test is eq:
        try:
            v = kvs[k]
            if setter:
                return lambda v: xset(kvs, k, v)
            else:
                return v
        except KeyError:
            return unset
        except TypeError:
            # unhashable k
            pass
    for key in kvs:
        if test(key, k):
            if setter:
                return lambda v: xset(kvs, key, v)
            else:
                return kvs[key]
    return unset

@get.register(py.tuple)
@get.register(py.list)
def get_seq(ls: Sequence[std.Mapping], k, test=equal, setter=nil):
    if accessor(k) or number(k) or isinstance(k, py.slice):
        return grab(ls, k, setter=setter)
    for l in ls:
        if not unset(it := get(l, k, test, setter=setter)):
            return it
    return unset

"""
(set smark (join))
"""
smark = globals().setdefault("smark", join("%smark"))

"""
(mac fu args
  `(list (list smark 'fut (fn ,@args)) nil))
"""

def fut(a, *args, **kws):
    def futa(f):
        return list(list(smark, "fut", f, *args, kws or nil), a)
    return futa

def evmark(e, a, s, r, m):
    """
    (def evmark (e a s r m)
      (case (car e)
        fut  ((cadr e) s r m)
        bind (mev s r m)
        loc  (sigerr 'unfindable s r m)
        prot (mev (cons (list (cadr e) a)
                        (fu (s r m) (mev s (cdr r) m))
                        s)
                  r
                  m)
             (sigerr 'unknown-mark s r m)))
    """
    it = car(e)
    if eq(it, "fut"):
        return cadr(e)(s, r, m)
    if eq(it, "bind"):
        assert begins(s[-1][0], [smark, "bind", nil])
        return mev(s[:-1], r, m)
    return sigerr("unknown-mark", s, r, m)

"""
(set forms (list (cons smark evmark)))
"""
def form(e):
    def setter(f):
        forms[e] = f
        return f
    return setter

forms = globals().setdefault("forms", {})

forms[smark] = evmark

def discard(s, r, m):
    return mev(s, cdr(r), m)

@form("do")
def do(es, a, s, r, m):
    e, es = car(es), cdr(es)
    if no(es):
        return mev(cons(list(e, a), s), r, m)
    else:
        return mev(cons(list(e, a),
                        fut(a, e)(discard),
                        list(cons("do", es), a),
                        s),
                   r,
                   m)

def quoted(x):
    if pair(x):
        return list("list" if proper(x) else "cons", *map(quoted, mkproper(x)))
    # elif eq(x, "t"):
    #     return t
    # elif eq(x, "nil"):
    #     return nil
    # elif eq(x, "True"):
    #     return True
    # elif eq(x, "False"):
    #     return False
    # elif eq(x, "unset"):
    #     return unset
    else:
        # if literal(x):
        #     if not string(x):
        #         return x
        if numeric_literal(x):
            try:
                return ast.literal_eval(x)
            except ValueError:
                pass
        elif literal(x) and not string_literal(x) and not id_literal(x):
            return x
    return list("%quote", x)

@form("%quote")
def quote2(es, a, s, r, m):
    """
    (form quote ((e) a s r m)
      (mev s (cons e r) m))
    """
    e = car(es)
    # print("quoting", e)
    e = quoted(e)
    # print("quoted", e)
    # return mev(s, cons(e, r), m)
    return mev(cons(list(e, a), s), r, m)

@form("quote")
def quote1(es, a, s, r, m):
    e = car(es)
    return mev(s, cons(e, r), m)

def if_(cond, then, else_):
    return then if cond else else_

@form("if")
def if1(es, a, s, r, m):
    """
    (form if (es a s r m)
      (if (no es)
          (mev s (cons nil r) m)
          (mev (cons (list (car es) a)
                     (if (cdr es)
                         (cons (fu (s r m)
                                 (if2 (cdr es) a s r m))
                               s)
                         s))
               r
               m)))
    """
    @fut(a, cons("if", es))
    def if_then_else(s, r, m):
        return if2(cdr(es), a, s, r, m)
    return if_(no(es),
               lambda: mev(s, cons(nil, r), m),
               lambda: mev(cons(list(car(es), a),
                                if_(cdr(es),
                                    lambda: cons(if_then_else, s),
                                    lambda: s)()),
                           r,
                           m))()

def if2(es, a, s, r, m):
    """
    (def if2 (es a s r m)
      (mev (cons (list (if (car r)
                           (car es)
                           (cons 'if (cdr es)))
                       a)
                 s)
           (cdr r)
           m))
    """
    return mev(cons(list(if_(car(r),
                             lambda: car(es),
                             lambda: cons("if", cdr(es)))(),
                         a),
                    s),
               cdr(r),
               m)

"""
(form where ((e (o new)) a s r m)
  (mev (cons (list e a)
             (list (list smark 'loc new) nil)
             s)
       r
       m))
"""

@form("dyn")
def dyn(es, a, s, r, m):
    """
    (form dyn ((v e1 e2) a s r m)
      (if (variable v)
          (mev (cons (list e1 a)
                     (fu (s r m) (dyn2 v e2 a s r m))
                     s)
               r
               m)
          (sigerr 'cannot-bind s r m)))
    """
    # v, e1, e2 = car(es), cadr(es), cons("do", cddr(es))
    [v, e1, *body] = es
    e2 = cons("do", body)
    if variable(v):
        @fut(a, cons("dyn", es))
        def dyn(s, r, m):
            return dyn2(v, e2, a, s, r, m)
        return mev(cons(list(e1, a),
                        dyn,
                        s),
                   r,
                   m)
    else:
        return sigerr(list("cannot-bind", v, e1), s, r, m)

def dyn2(v, e2, a, s, r, m):
    """
    (def dyn2 (v e2 a s r m)
      (mev (cons (list e2 a)
                 (list (list smark 'bind (cons v (car r)))
                       nil)
                 s)
           (cdr r)
           m))
    """
    cell = {v: car(r)}
    return mev(snoc(cons(list(e2, a),
                         # list(list(smark, "bind", list(v, car(r))),
                         list(list(smark, "bind", cell),
                              a),
                         s),
                    list(list(smark, "bind", nil), a)),
               cdr(r),
               m)

@form("let")
def let1(es, a, s, r, m):
    [v, e1, *body] = es
    e2 = cons("do", body)
    if variable(v):
        @fut(a, cons("let", es))
        def let(s, r, m):
            return let2(v, e2, a, s, r, m)
        return mev(cons(list(e1, a),
                        let,
                        s),
                   r,
                   m)
    else:
        return sigerr(list("cannot-let", v, e1), s, r, m)

def let2(v, e2, a, s, r, m):
    cell = {v: car(r)}
    env = cons(cell, a)
    return mev(cons(list(e2, env),
                    s),
               cdr(r),
               m)

"""
(form after ((e1 e2) a s r m)
  (mev (cons (list e1 a)
             (list (list smark 'prot e2) a)
             s)
       r
       m))
"""

@form("ccc")
def ccc(es, a, s, r, m):
    """
    (form ccc ((f) a s r m)
      (mev (cons (list (list f (list 'lit 'cont s r))
                       a)
                 s)
           r
           m))
    """
    f = car(es)
    return mev(cons(list(list(f, list("lit", "cont", s, r)),
                         a),
                    s),
               r,
               m)

@form("thread")
def thread(es, a, s, r, m):
    """
    (form thread ((e) a s r (p g))
      (mev s
           (cons nil r)
           (list (cons (list (list (list e a))
                             nil)
                       p)
                 g)))
    """
    e = cons("do", es)
    p, g = car(m), cadr(m)
    return mev(s,
               cons(nil, r),
               list(cons(list(list(list(e, a)),
                              nil),
                         p),
                    g))

def evcall(e, a, s, r, m):
    """
    (def evcall (e a s r m)
      (mev (cons (list (car e) a)
                 (fu (s r m)
                   (evcall2 (cdr e) a s r m))
                 s)
           r
           m))
    """
    @fut(a, e)
    def calling(s, r, m):
        return evcall2(cdr(e), a, s, r, m)

    return mev(cons(list(car(e), a),
                    calling,
                    s),
               r,
               m)

def evcall2(es, a, s, r, m):
    """
    (def evcall2 (es a s (op . r) m)
      (if ((isa 'mac) op)
          (applym op es a s r m)
          (mev (append (map [list _ a] es)
                       (cons (fu (s r m)
                               (let (args r2) (snap es r)
                                 (applyf op (rev args) a s r2 m)))
                             s))
               r
               m)))
    """
    op, r = car(r), cdr(r)
    if begins(op, ("lit", "mac")):
        kws = {}
        args, rest = snap(es, rev(es), kws)
        print("applym", op, args, kws)
        return applym(op, args, kws, a, s, r, m)

    @fut(a, cons(op, es))
    def applying(s, r, m):
        kws = {}
        args, r2 = snap(es, r, kws)
        # args = rev(args)
        return applyf(op, args, kws, a, s, r2, m)

    return mev(append(map(lambda x: list(x, a), es or ()),
                      cons(applying, s)),
               r,
               m)

def snap(es, r, kws=unset):
    """
    (def snap (xs ys (o acc))
      (if (no xs)
          (list acc ys)
          (snap (cdr xs) (cdr ys) (snoc acc (car ys)))))
    """
    kws = init(kws, lambda: {})
    n = len(es or [])
    r = r or []
    lh, rh = r[:n], r[n:]
    lh = rev(lh)
    args = []
    i = 0
    while i < n:
        if keyword(es[i]):
            k = keyword_name(es[i])
            v = grab(lh, i + 1)
            kws[k] = v
            i += 2
        else:
            args.append(lh[i])
            i += 1
    # while len(es) >= 2 and keyword(es[-2]):
    #     kws[keyword_name(es[-2])] = lh[-1]
    #     lh = lh[:-2]
    #     es = es[:-2]
    return args, rh

def rev(es):
    """
    (def rev (xs)
      (if (no xs)
          nil
          (snoc (rev (cdr xs)) (car xs))))
    """
    return es[::-1] if es else nil


def applym(mac, args, kws, a, s, r, m):
    """
    (def applym (mac args a s r m)
      (applyf (caddr mac)
              args
              a
              (cons (fu (s r m)
                      (mev (cons (list (car r) a) s)
                           (cdr r)
                           m))
                    s)
              r
              m))
    """
    @fut(a, cons(caddr(mac), args))
    def expanding(s, r, m):
        return mev(cons(list(car(r), a), s),
                   cdr(r),
                   m)

    return applyf(caddr(mac),
                  args,
                  kws,
                  a,
                  cons(expanding,
                       s),
                  r,
                  m)

def applyf(f, args, kws, a, s, r, m):
    """
    (def applyf (f args a s r m)
      (if (= f apply)    (applyf (car args) (reduce join (cdr args)) a s r m)
          (caris f 'lit) (if (proper f)
                             (applylit f args a s r m)
                             (sigerr 'bad-lit s r m))
                         (sigerr 'cannot-apply s r m)))
    """
    if callable(f):
        e = apply(f, args, kws)
        return mev(s, cons(e, r), m)
    if caris(f, "lit"):
        return applylit(f, args, kws, a, s, r, m)
    return sigerr(list("cannot-apply", cons(f, args, kws)), s, r, m)

def applylit(f, args, kws, a, s, r, m):
    """
    (def applylit (f args a s r m)
      (aif (and (inwhere s) (find [(car _) f] locfns))
           ((cadr it) f args a s r m)
           (let (tag . rest) (cdr f)
             (case tag
               prim (applyprim (car rest) args s r m)
               clo  (let ((o env) (o parms) (o body) . extra) rest
                      (if (and (okenv env) (okparms parms))
                          (applyclo parms args env body s r m)
                          (sigerr 'bad-clo s r m)))
               mac  (applym f (map [list 'quote _] args) a s r m)
               cont (let ((o s2) (o r2) . extra) rest
                      (if (and (okstack s2) (proper r2))
                          (applycont s2 r2 args s r m)
                          (sigerr 'bad-cont s r m)))
                    (aif (get tag virfns)
                         (let e ((cdr it) f (map [list 'quote _] args))
                           (mev (cons (list e a) s) r m))
                         (sigerr 'unapplyable s r m))))))
    """
    lit = cdr(f)
    tag, rest = car(lit), cdr(lit)
    if eq(tag, "mac"):
        return applym(f, [list("quote", x) for x in args or ()], kws, a, s, r, m)
        # return applym(f, args or (), a, s, r, m)
    if eq(tag, "cont"):
        s2, r2 = car(rest), cadr(rest)
        return applycont(s2, r2, args, s, r, m)
    return sigerr(list("unapplyable", cons(f, args)))

def applycont(s2, r2, args, s, r, m):
    """
    (def applycont (s2 r2 args s r m)
      (if (or (no args) (cdr args))
          (sigerr 'wrong-no-args s r m)
          (mev (append (keep [and (protected _) (no (mem _ s2 id))]
                             s)
                       s2)
               (cons (car args) r2)
               m)))
    """
    if no(args) or cdr(args):
        return sigerr(list("wrong-no-args", args), s, r, m)
    # return mev(s2,
    #            cons(car(args), r2),
    #            m)
    return mev(append(keep(lambda x: protected(x) and not mem(x, s2, eq),
                           s),
                      s2),
               cons(car(args), r2),
               m)

def protected(x):
    """
    (def protected (x)
      (some [begins (car x) (list smark _) id]
            '(bind prot)))
    """
    for tag in ["bind", "prot"]:
        if begins(car(x), list(smark, tag), eq):
            return t


import code
import codeop

class BelCommandCompiler(codeop.CommandCompiler):
    def __call__(self, source, filename="<input>", symbol="single"):
        form, pos = reader.read_from_string(source, more=(more := object()), mode="bel")
        if form is more:
            return None
        return form

class BelConsole(code.InteractiveConsole):
    def __init__(self, locals=unset, filename="<console>"):
        super().__init__(locals={}, filename=filename)
        self.locals = locals
        self.compile = BelCommandCompiler()
        self.that = nil
        self.thatexpr = nil

    def exec(self, form, locals=unset):
        if locals is unset:
            locals = self.locals
        # print(json.dumps(form))
        self.thatexpr = form
        self.that = bel(self.thatexpr, unset, locals)
        if self.that is not None:
            print(repr(self.that))

    def runcode(self, code):
        """Execute a code object.

        When an exception occurs, self.showtraceback() is called to
        display a traceback.  All exceptions are caught except
        SystemExit, which is reraised.

        A note about KeyboardInterrupt: this exception may occur
        elsewhere in this code, and may not always be caught.  The
        caller should be prepared to deal with it.

        """
        import yel
        import yel.constants
        reload(yel.constants)
        reload(yel.util)
        reload(reader)
        reload(compiler)
        reload(yel.bel)
        reload(M)
        try:
            self.exec(code, self.locals)
        except SystemExit:
            raise
        except:
            self.showtraceback()

@contextlib.contextmanager
def letattr(obj, key, val):
    empty = object()
    prev = getattr(obj, key, empty)
    setattr(obj, key, val)
    try:
        yield
    finally:
        if prev is empty:
            delattr(obj, key)
        else:
            setattr(obj, key, prev)

def interact(*, banner=None, readfunc=None, local=None, exitmsg=None):
    """Closely emulate the interactive Python interpreter.

    This is a backwards compatible interface to the InteractiveConsole
    class.  When readfunc is not specified, it attempts to import the
    readline module to enable GNU readline if it is available.

    Arguments (all optional, all default to None):

    banner -- passed to InteractiveConsole.interact()
    readfunc -- if not None, replaces InteractiveConsole.raw_input()
    local -- passed to InteractiveInterpreter.__init__()
    exitmsg -- passed to InteractiveConsole.interact()

    """
    console = BelConsole(local)
    if readfunc is not None:
        console.raw_input = readfunc
    else:
        try:
            import readline
        except ImportError:
            pass
    iterm2_prompt_mark = "\u001b]133;A\u0007\n"
    with letattr(sys, 'ps1', iterm2_prompt_mark + '> '):
        with letattr(sys, 'ps2', '  '):
            console.interact(banner, exitmsg)


def dbg():
    import pdb
    pdb.pm()


def read_file(filename):
    with open(filename, "r") as f:
        return f.read()

def write_file(filename, data):
    with util.open_atomic(filename, "w") as f:
        f.write(data)

def read_from_file(filename, *, mode="bel"):
    code = read_file(filename)
    body = reader.read_all(reader.stream(code, mode=mode))
    return body

def compile_file(filename):
    body = read_from_file(filename)
    return mapcat(compiler.compile_statement, body)

def load(filename):
    filepath = os.path.realpath(filename)
    base, ext = os.path.splitext(filepath)
    assert ext == ".l"
    fileout = base + ".py"
    print(fileout)
    compiled = compile_file(filepath)
    write_file(fileout, compiled)


# import yel.bel as b; from importlib import reload; reload(b)
# x = 2
# zz = 42
# reload(b); f, (s, r, m) = b.bel(['do', 1, 2, ['do', 3, 4, 5], ['do', 1, 2, 'x', ['print', ["list", 1, 2]], ["list", 3, 4, "zz", ["+", 3, "zz"]]]], globals()); b.wait(f, s, r, m)
