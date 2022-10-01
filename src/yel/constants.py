from __future__ import annotations
from typing import *
from typing_extensions import ParamSpec
from functools import singledispatch as dispatch
import numbers
import builtins as py
import contextvars as CV
import contextlib
import collections.abc as std
import collections

T = TypeVar('T')  # Any type.
R = TypeVar('R')  # Return type.
P = ParamSpec("P") # Function params.
KT = TypeVar('KT')  # Key type.
VT = TypeVar('VT')  # Value type.
T_co = TypeVar('T_co', covariant=True)  # Any type covariant containers.
V_co = TypeVar('V_co', covariant=True)  # Any type covariant containers.
VT_co = TypeVar('VT_co', covariant=True)  # Value type covariant containers.
T_contra = TypeVar('T_contra', contravariant=True)  # Ditto contravariant.
KT_contra = TypeVar('KT_contra', contravariant=True)  # Ditto contravariant.
# Internal type variable used for Type[].
CT_co = TypeVar('CT_co', covariant=True, bound=type)

t = True
nil = None

class Unset:
    def __bool__(self):
        return False

    def __repr__(self):
        return "unset"

    def __eq__(self, other):
        return other is unset

    def __call__(self, *x):
        return x[0] is unset if x else unset

unset = Unset()

def ncar(l: List[T]) -> Optional[T]:
    if l:
        return l.pop(0)

def ncons(x: T, l: List[T]) -> List[T]:
    l = l or []
    l.insert(0, x)
    return l

def nsnoc(l: List[T], x: T) -> List[T]:
    l = l or []
    l.append(x)
    return l

@runtime_checkable
class SupportsGetItem(Container[KT_contra], Protocol[KT_contra, VT_co]):
    def __getitem__(self, __k: KT_contra) -> VT_co: ...

# def car(l: Optional[SupportsGetItem[T]]) -> Optional[T]:
# def car(l: Optional[Sequence[T]]) -> Optional[T]:
def car(l: Optional[Container[T]]) -> T:
    if l:
        return l[0]

def car_safe(l: Optional[Container[T]]) -> Optional[T]:
    if sequence(l) and l:
        return l[0]

assert car(nil) == nil
assert car([]) == nil
assert car([1]) == 1

# def cdr(l: Optional[SupportsGetItem[T]]) -> Optional[SupportsGetItem[T]]:
def cdr(l: Optional[Container[T]]) -> Optional[Container[T]]:
    if l:
        if v := l[1:]:
            if v[0] == ".":
                if isinstance(l, (tuple, list)):
                    if len(l) == 3 and l[1] == ".":
                        return l[2]
            return v

assert cdr(nil) == nil
assert cdr([]) == nil
assert cdr([1]) == nil
assert cdr([1, ".", 2]) == 2

def sequence(x):
    return isinstance(x, (py.list, py.tuple))

class Seq(list):
    def __hash__(self):
        return hash(py.id(self))

def join(x=nil, y=nil):
    if not isinstance(y, (str, bytes)):
        try:
            return Seq([x, *(y or [])])
        except TypeError:
            pass
    return Seq([x, ".", y])

assert join(nil, nil) == [nil], f"{join(nil, nil)=} != [nil]"
assert join(1, 2) == [1, ".", 2]
assert join(1, '"foo"') == [1, ".", '"foo"']

def init(x: T, val: Callable[[], T] = lambda: t) -> T:
    if unset(x):
        return val()
    return x

def identical(x, y):
    if x is y:
        return t

@dispatch
def eq(x, y):
    return identical(x, y)

import operator

def boolean(x):
    return isinstance(x, bool)

def string(x):
    return isinstance(x, str)

def number(e):
    if isinstance(e, numbers.Number):
        if not isinstance(e, bool):
            return t

eq.register(bool, identical)

@eq.register(str)
@eq.register(bytes)
@eq.register(int)
@eq.register(float)
def eqv(x, y):
    if x == y:
        if boolean(y):
            return identical(x, y)
        return t

def idfn(x):
    return x

def map(f, *args):
    return py.list(py.map(f, *(l or () for l in args)))

def mapcat(f, *args, sep=""):
    r = []
    for x in map(f or idfn, *args):
        if x is not nil:
            r.append(py.str(x))
    return sep.join(r)

def cat(*args, sep=""):
    return mapcat(nil, args, sep=sep)

def numeric_literal(e):
    if e and string(e):
        if e[0].isdigit() or e[0] in ["-", "+"] and e[1:] and e[1].isdigit():
            return t

def string_literal(e, c='"'):
    if e and string(e):
        if e.startswith(c) and e.endswith(c) and e != c:
            return t

def accessor(k):
    if k and string(k) and k[0] == ".":
        return t

def accessor_name(k):
    if accessor(k):
        # return compiler.compile_id(k[1:])
        return k[1:]
    if string(k):
        return k

def keyword(k):
    if k and string(k) and k[0] == ":":
        return t

def keyword_name(k):
    if keyword(k):
        return k[1:]

@contextlib.contextmanager
def CV_let(var: CV.ContextVar[T], val: T):
    prev = var.set(val)
    try:
        yield
    finally:
        var.reset(prev)

def at(l, k, default=nil):
    try:
        return l[k]
    except (LookupError, TypeError):
        return default

def carp(l, k):
    return eq(car_safe(l), k)
