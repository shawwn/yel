from __future__ import annotations
from typing import *
import collections.abc as std
import builtins as py
import contextlib
import itertools

from .constants import *

def apply(f, args=nil, kws: Mapping = nil):
    return f(*(args or []), **(kws or {}))

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
    for x in xs:
        if f(x):
            return xs

def all(f, xs):
    for x in xs:
        if not f(x):
            return nil
    return xs

def string(e):
    if isinstance(e, str):
        return t

def number(e):
    if isinstance(e, numbers.Number):
        if not isinstance(e, bool):
            return t

def pair(x):
    if x and isinstance(x, (py.list, py.tuple)):
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

def bel(e, g: List[Dict] = unset, a: List[MutableMapping] = unset):
    """
    (def bel (e (o g globe))
      (ev (list (list e nil))
          nil
          (list nil g)))
    """
    g = [init(g, lambda: [globals(), py.__dict__])]
    a = [init(a, lambda: [])]
    return tev(ev,
               [[e, a]],
               [],
               [[], g])

def tev(f, s: List[List], r: List, m: Tuple[List, Dict]):
    while it := f(s, r, m):
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
        return sched(snoc(p, [s, r]), g)

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
        return mev(s, cons(e, r), m)
    if variable(e):
        return vref(e, a, s, r, m)
    # print()
    # print("> ", e, s, r)
    if it := get(forms, car(e), eq):
        return cadr(it)(cdr(e), a, s, r, m)
    if callable(car(e)):
        return evcall2(cdr(e), a, s, cons(car(e), r), m)
    return evcall(e, a, s, r, m)

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
    g = cadr(m)
    if it := lookup(v, a, s, g):
        return mev(s, cons(cadr(it), r), m)
    else:
        return sigerr(list("unboundb", v), s, r, m)

def lookup(e, a, s, g):
    """
    (def lookup (e a s g)
      (or (binding e s)
          (get e a id)
          (get e g id)
          (case e
            scope (cons e a)
            globe (cons e g))))
    """
    if it := binding(e, s):
        return it
    if it := get(a, e, eq):
        return it
    if it := get(g, e, eq):
        return it
    if eq(e, "scope"):
        return list(a, a)
    if eq(e, "globe"):
        return list(g, g)

def binding(v, s):
    """
    (def binding (v s)
      (get v
           (map caddr (keep [begins _ (list smark 'bind) id]
                            (map car s)))
           id))
    """
    pat = [smark, "bind"]
    for [e, a] in s or ():
        if begins(e, pat, eq):
            cell = caddr(e)
            if caris(cell, v):
                return cell

def sigerr(msg, s, r, m):
    """
    (def sigerr (msg s r m)
      (aif (binding 'err s)
           (applyf (cdr it) (list msg) nil s r m)
           (err 'no-err)))
    """
    raise ValueError(msg, s, r)

def string_literal(e, c='"'):
    if e and string(e):
        if e.startswith(c) and e.endswith(c) and e != c:
            return t

def id_literal(e):
    return string_literal(e, "|")

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
    elif pair(e):
        return nil
    elif callable(e):
        return t
    elif string_literal(e):
        return t
    elif id_literal(e):
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

"""
(def uvar ()
  (list vmark))
"""
def uvar(*info):
    return list(vmark, *info)

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

@dispatch
def get(kvs, k, test=equal):
    raise NotImplementedError("get", kvs, k, test)

@get.register(type(None))
def get_nil(kvs: None, k, test=equal):
    pass

@get.register(std.Mapping)
def get_Mapping(kvs: Mapping, k, test=equal):
    if test is eq:
        try:
            it = k in kvs
        except TypeError:
            # unhashable k
            pass
        else:
            if it:
                return kvs, kvs[k]
    for key in kvs:
        if test(key, k):
            return kvs, kvs[key]

@get.register(py.tuple)
@get.register(py.list)
def get_seq(ls: Sequence[std.Mapping], k, test=equal):
    for l in ls:
        if it := get(l, k, test):
            return it

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
        return mev(s, r, m)
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

@fut(nil)
def discard(s, r, m):
    return mev(s, cdr(r), m)

@form("do")
def do(es, a, s, r, m):
    e, es = car(es), cdr(es)
    if no(es):
        return mev(cons(list(e, a), s), r, m)
    else:
        return mev(cons(list(e, a),
                        discard,
                        list(cons("do", es), a),
                        s),
                   r,
                   m)

@form("quote")
def quote(es, a, s, r, m):
    """
    (form quote ((e) a s r m)
      (mev s (cons e r) m))
    """
    return mev(s, cons(car(es), r), m)

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
        def let(s, r, m):
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
    return mev(cons(list(e2, a),
                    list(list(smark, "bind", cons(v, car(r))),
                         a),
                    s),
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
    env = cons({v: car(r)}, a)
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

    @fut(a, cons(op, es))
    def applying(s, r, m):
        args, r2 = snap(es, r)
        return applyf(op, rev(args), a, s, r2, m)

    return mev(append(map(lambda x: list(x, a), es or []),
                      cons(applying, s)),
               r,
               m)

def snap(es, r):
    """
    (def snap (xs ys (o acc))
      (if (no xs)
          (list acc ys)
          (snap (cdr xs) (cdr ys) (snoc acc (car ys)))))
    """
    n = len(es or [])
    r = r or []
    return r[:n], r[n:]

def rev(es):
    """
    (def rev (xs)
      (if (no xs)
          nil
          (snoc (rev (cdr xs)) (car xs))))
    """
    return es[::-1] if es else nil


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

def applyf(f, args, a, s, r, m):
    """
    (def applyf (f args a s r m)
      (if (= f apply)    (applyf (car args) (reduce join (cdr args)) a s r m)
          (caris f 'lit) (if (proper f)
                             (applylit f args a s r m)
                             (sigerr 'bad-lit s r m))
                         (sigerr 'cannot-apply s r m)))
    """
    if callable(f):
        e = f(*args)
        return mev(s, cons(e, r), m)
    if caris(f, "lit"):
        return applylit(f, args, a, s, r, m)
    return sigerr(list("cannot-apply", cons(f, args)), s, r, m)

def applylit(f, args, a, s, r, m):
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
    tag = car(lit)
    rest = cdr(lit)
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




# import yel.bel as b; from importlib import reload; reload(b)
# x = 2
# zz = 42
# reload(b); f, (s, r, m) = b.bel(['do', 1, 2, ['do', 3, 4, 5], ['do', 1, 2, 'x', ['print', ["list", 1, 2]], ["list", 3, 4, "zz", ["+", 3, "zz"]]]], globals()); b.wait(f, s, r, m)
