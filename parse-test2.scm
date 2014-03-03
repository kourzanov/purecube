#! /usr/bin/env bgl
; the beginning
(cond-expand (bigloo-eval
(module parse-test2
   (library srfi1 slib minikanren)
   (import ;brackets
	   (synrules "synrules.sch")
	   (helpers "helpers.scm")
	   (ascript "cases.scm")
	   (loprog "loprog.sch")
	   (purecube "purecube.scm"))
   (eval (export-exports)))
)(else
(module parse-test2
   (library srfi1 slib minikanren)
   (main main)
   )
(load "synrules.sch")
(load "dodger.sch")
(load "cases.scm")
(load "cond-expand.sch")
(load "forall.scm")
(load "helpers.scm")
(load "brace-syntax.sch")
(load "bracket-syntax.sch")
(load "loprog.sch")
(load "purecube.scm")
))

(pcg num extend: extend ([|.|] <=> ((#\0 / #\1) +)))
;(pcg (num extend: extend ([|.|] <=> ((#\0 / #\1) +))))

(def [char-tests]
   (verify num (map list->string
     (run* (q) (num (string->list "0102") '(#\2) q)))
      ===> "010")
   )

;(def test (predicate
(predicate test
([_ `() `()])
([_ `([,n . ,va] . ,ar) `([,n . ,vb] . ,br)] :-
 ((== va vb) /
  (== 'xxx vb))
 (test ar br))
; ([_ `([,n1 . ,va] . ,ar) `([,n2 . ,vb] . ,br)] :-
;  ((: (== va vb) (== n1 n2)) /
;   (: (== 'xxx vb) (== n1 n2)))
;  (test ar br))
; ([_ `([,n . ,va] . ,ar) `([,n . ,vb] . ,br)] :-
;  (== 'xxx vb)
;  (test ar br))
)
;)

(def [pred-tests]
   (pp (run* (q) (test '([1 . 2] [3 . 4]) q)))
   )

(pcg foo heads: (rev: symbol)
   ([_ x] <=> ((: 'a ((: 's [symbol x]) *)) *))
   )

(pcg bar heads: (rev: symbol)
   ([_ x] <=> (((: 's [symbol x]) *) *))
   )

(def [foo-tests]
   (pp (run* (q) (foo '(a s x s y s z a s b s c s d) '() q)))
   ;(pp (run* (q) (bar '(s x s y s z s b s c s d) '() q)))
   ;(pp (run* (q) (foo q '() '(((x y z) (b c d))))))
   )

(def [main argv]
     (display "hello CCGs")(newline)
     [char-tests]
     [pred-tests]
     [foo-tests]
 )

(cond-expand (bigloo-eval
 (main '())
)(else))
; the end