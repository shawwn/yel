(from __future__ import annotations)
; (let zz (Macro (fn (filename) (let e (compile_file (|compiler.unescape| filename)) (print "%file: " (|compiler.unescape| filename)) (print e) (mapcat nil (list "|" e "|"))))) |require = zz|)
;(from yel import importer)
;(from yel.lib import __main__)
(from yel.bel import *)
(from yel.reader import read_from_string as readstr)
(import operator)
(import functools)
(import itertools)
(import builtins as py)
(from numbers import Number)

(from typing import *)


;(do |
;def pairwise(iterable):
;    # pairwise('ABCDEFG') --> AB BC CD DE EF FG
;    a, b = itertools.tee(iterable)
;    py.next(b, None)
;    return py.zip(a, b)
;|)

;(def pairwise (iterable: (get Iterable T)) -> (get Generator (get Tuple T T))
(def pairwise (iterable: Iterable[T]) -> (py .zip)[Tuple[T T]]
  (set (a, b) (itertools (.tee iterable)))
  (py (.next b nil))
  (return (py (.zip a b))))

(def reduce (f: Callable[[T Union[T R]] R] args: Optional[Sequence[T]]) -> Union[T R]
  (if (cdr args)
      (return (f (car args) (reduce f (cdr args))))
      (return (car args))))

(def either (x: Optional[T] y: T) -> T
  (if (unset x) (return y) (return x)))

;(for k in '(+)
;  (set (get (globals) k) (get (bel .bel .__globals__) k)))

;(set (get (globals) "+") (operator .add))
;(set (get (globals) "-") (operator .sub))
;(set (get (globals) "*") (operator .mul))
;(set (get (globals) "/") (operator .truediv))
;(set (get (globals) "//") (operator .floordiv))


;(def none? (x) ((bel
;
;(def reduce (f *args)
;  ()
;
;
;
;
;  )

;(def = (*args)
;     (for a, b in (pairwise args)
;       (if (no (%infix a == b))
;           (return nil)))
;     (return t))


;(set (%array x, y), z (%array 1, 2), 3)





;;(def + (*args) (return (functools (.reduce (fn (a b) (%infix a + b)) args 0))))
;(def + (*args) (return (reduce (fn (a b) (%infix a + b)) |args or [1]|)))
;(def - (*args) (return (reduce (fn (b a) (%infix b - a)) (reversed |args or [1]|))))
;(def * (*args) (return (functools (.reduce (fn (a b) (%infix a * b)) args 1))))
;(def - (*args) (return (functools (.reduce (fn (b a) (%infix a - b)) (reversed args) 0))))
;(def / (*args) (return (functools (.reduce (fn (b a) (%infix a / b)) (reversed args) 1))))
;(def // (*args) (return (functools (.reduce (fn (b a) (%infix a // b)) (reversed args) 1))))


(print "hi")

(def foo (x: T) -> T
  (return (+ x 1)))

;(defmacro class
;  "docstring"
;  [arglist & body]
;  )

(class Bar ()
  (def __init__ (self x: Number y: Number)
    (set (self .x) x)
    (set (self .y) y))

  (@ property)
  (def name (self) -> str
    (return (repr (list (self .x) (self .y))))))

(def readfile (filename: str) -> str
  (with (open filename) as f
    (return (f (.read)))))



(print ((fn (x) (+ x 1)) 2))

(import asyncio as aio)
(import asyncstdlib as a)

;(set f (fn (x) (+ x 1)))

(print __name__)
(print __file__)

;(mac nilwith (x)
;  (list 'cons 'nil x))
;
;(fn (x y) (+ x y))
;
;(let (a b c) (list 1 2 3)
;  a)
;
;(for k, v in((globals) (.items))
;  )
(when (= __name__ "__main__")
  (Bar 1 2)
  (Bar "x" "y")
  (Bar 1 'a)
  (for k, v in ((globals) (.items))
    (print k))
  (after (print 'first)
    (print 'second)))
