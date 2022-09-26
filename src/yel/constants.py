from __future__ import annotations
from typing import *
from functools import singledispatch as dispatch
import numbers
import builtins as py

T = TypeVar("T")

t = True
nil = None

class Unset:
    def __bool__(self):
        return False

    def __repr__(self):
        return "unset"

    def __eq__(self, _other):
        return False

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

def car(l: Optional[Sequence[T]]) -> Optional[T]:
    if l:
        return l[0]

assert car(nil) == nil
assert car([]) == nil
assert car([1]) == 1

def cdr(l: Optional[T]) -> Optional[T]:
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

class Seq(list):
    def __hash__(self):
        return hash(py.id(self))

def join(x=nil, y=nil):
    try:
        return Seq([x, *(y or [])])
    except TypeError:
        return Seq([x, ".", y])

assert join(nil, nil) == [nil], f"{join(nil, nil)=} != [nil]"
assert join(1, 2) == [1, ".", 2]

def init(x: T, val: Callable[[], T] = lambda: t) -> T:
    if unset(x):
        return val()
    return x

@dispatch
def eq(x, y):
    if x is y:
        return t

import operator

eq.register(bool, operator.is_)

def boolean(x):
    return isinstance(x, bool)

@eq.register(str)
@eq.register(bytes)
@eq.register(int)
@eq.register(float)
def eqv(x, y):
    if boolean(y):
        return nil
    if x == y:
        return t