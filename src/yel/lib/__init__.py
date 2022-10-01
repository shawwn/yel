from __future__ import annotations

from yel.bel import *

from yel.reader import read_from_string as readstr

import operator

import functools

import itertools

import builtins as py

from numbers import Number

from typing import *

def pairwise(iterable: Iterable[T]) -> py.zip[Tuple[T, T]]:
    (a, b) = itertools.tee(iterable)
    py.next(b, nil)
    return py.zip(a, b)

def reduce(f: Callable[[T, Union[T, R]], R], args: Optional[Sequence[T]]) -> Union[T, R]:
    if cdr(args):
        return f(car(args), reduce(f, cdr(args)))
    else:
        return car(args)

def either(x: Optional[T], y: T) -> T:
    if unset(x):
        return y
    else:
        return x

print("hi")

def foo(x: T) -> T:
    return x + 1

class Bar:
    def __init__(self, x: Number, y: Number):
        self.x = x
        self.y = y
    @property
    def name(self) -> str:
        return repr(list(self.x, self.y))

def readfile(filename: str) -> str:
    with open(filename) as f:
        return f.read()

print((lambda x: x + 1)(2))

import asyncio as aio

import asyncstdlib as a

print(__name__)

print(__file__)

if __name__ == "__main__":
    Bar(1, 2)
    Bar("x", "y")
    Bar(1, "a")
    for (k, v) in globals().items():
        print(k)
    try:
        print("first")
    finally:
        print("second")

