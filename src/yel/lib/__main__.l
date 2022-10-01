;(from yel import importer)
;(from yel.lib import __main__)
;(from yel import lib)
;;(from yel import lib)
;;(from yel.lib import __main__)
;(from yel import compiler)
;(from yel import lib)
;(from yel.lib import __main__)
(from yel import importer)
(from yel import compiler)
(from yel.constants import *)
(from yel.lib import readfile)
(from yel.lib import __main__)

(from yel import lib)

;(mac when [& body]
;  ("%do", *body))
;
;(if (%not (= __name__ "__main__"))
;(if (not (= __name__ "__main__"))
;    (do
(def main ()
  (print __name__ (lib (.foo 2)))
  (print 26)
  (when t
        (print 'ok))
  (print 'o 'm 'g :sep "|" :end "end!" :flush t)
  (print)
  (print 'a 'b 'c))

(defmacro unless [x & body]
  x)

(unless (= __name__ '__main__)
  
        (main))
