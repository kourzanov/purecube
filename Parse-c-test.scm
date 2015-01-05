#! /usr/bin/env bgl
; the beginning
(cond-expand (bigloo-eval
(module Parse-c-test
   (library bkanren slib srfi1)
   (import (helpers "helpers.scm")
	   (loprog "loprog.sch")
	   (Parse "Parse.scm")
	   (ascript "cases.scm")
	   (Parse-c "Parse-c.scm")
   ))
)(else
(module Parse-c-test
   (library bkanren slib srfi1)
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
(load "Parse.scm")
(load "hack-syntax.sch")
(load "Parse-c.scm")
))

(def-syntax _ rcurry)
(def-syntax + $+)
(def-syntax - $-)
(def-syntax * $*)
(def-syntax / $/)

(bigloo-debug-set! 1)
;(bigloo-debug)

(pp (run* (q) ([ne-la-list-of symbol '|,|] '(a |,| b |,| c) '() q)))
(pp (run* (q) ([ne-la-seq-of symbol] '(a b c) '() q)))
(pp (run* (q) ([ne-ra-list-of symbol '|,|] '(a |,| b |,| c) '() q)))
(pp (run* (q) ([ne-ra-seq-of symbol] '(a b c) '() q)))


; XXX does no work somehow [[elem]] is possibly recursive
(def [ne-ra-list-of' elem comma] (pcg heads: (rev: elem)
  ([_ `(,v . ,vs)] <=> [elem v] [idem comma] [(ne-ra-list-of elem comma) vs])
  ([_ `(,v)] <=> [elem v])
 ))
(def [ne-ra-seq-of' elem] (pcg heads: (rev: elem)
  ([_ `(,v . ,vs)] <=> [elem v] [(ne-ra-seq-of elem) vs])
  ([_ `(,v)] <=> [elem v])
 ))
; left-recursive can not be defined this way (no way to check the higher-order function)
(def [ne-la-list-of' elem comma] (pcg heads: (rev: elem)
  ([_ `(,v . ,vs)] <=> [(ne-la-list-of elem comma) vs] [idem comma] [elem v])
  ([_ `(,v)] <=> [elem v])
 ))
; not used
(defn [list-of elem comma] (pcg heads: (reu: elem idem comma)
  ([_ '()] <=> ε)
  ([_ `(,v . ,vs)] <=> [elem v] [(: [idem comma] [elem vs]) *])
 ))


(def-syntax c-expr expression)

(if #true (begin
(pp (run* (q) (c-expr '#h: +  '() q)))
(pp (run* (q) (c-expr '#h: 1*(2+n)%5+"3"  '() q)))
(pp (run* (q) (c-expr '#h: a[1]  '() q)))
(pp (run* (q) (c-expr '#h: foobar()  '() q)))
(pp (run* (q) (c-expr '#h: foobar (1,2)  '() q)))
(pp (run* (q) (c-expr '#h: foobar((1,2))  '() q)))
(pp (run* (q) (c-expr '#h: quux.fubar  '() q)))
(pp (run* (q) (c-expr '#h: quux->fubar  '() q)))
(pp (run* (q) (c-expr '#h: b[a]++  '() q)))
(pp (run* (q) (c-expr '#h: b[++a]  '() q)))
(pp (run* (q) (c-expr '#h: +(int)12  '() q)))
(pp (run* (q) (c-expr '#h: 1 && 0  '() q)))
(pp (run* (q) (c-expr '#h: 1,2|3,3||0  '() q)))
(pp (run* (q) (c-expr '#h: x=y=1233  '() q)))
))


(def-syntax c-decl declaration)

(if #true (begin
(bigloo-debug-set! 3)
(pp (run 1 (q) (c-decl '#h: struct { int a,b; } c;  '() q)))
;(pp (run* (q) (c-decl '#h: a,b ...  '() q)))
(pp (run* (q) (c-decl '#h: int a,b;  '() q)))
(pp (run* (q) (c-decl '#h: int a=42;  '() q)))
(pp (run* (q) (c-decl '#h: int a=ENUM_CONST;  '() q)))
(register-enum 'ENUM_CONST)
(pp (run* (q) (c-decl '#h: int a=ENUM_CONST;  '() q)))
;(pp (run* (q) (c-decl '#h: int((*fp)(int(*)(int,int),int))(int,int);  '() q)))
(bigloo-debug-set! 1)
))

(def-syntax c-stmt statement)

(if #true (begin
(bigloo-debug-set! 3)
(pp (run* (q) (c-stmt '#h: _Static_assert(x?y:z,"xyz");  '() q)))
;(pp (run 1 (q) (c-stmt '#h: x[i]=10;  '() q)))
(bigloo-debug-set! 5)
(pp (run* (q) (c-stmt '#h: for (i=0; i<10; i++);  '() q)))
;(pp (run 1 (q) (c-stmt '#h: for (i=0; i<10; i++) { x[i]=10; }  '() q)))
;(pp (run* (q) (compound_statement '#h: {int i; for (i=0; i<10; i++);}  '() q)))
;(pp (run* (q) (translation_unit '#h: int foo() {}  '() q)))
;(pp (run* (q) (translation_unit '#h: int foo() { int i; for (i=0; i<10; i++); }  '() q)))
(bigloo-debug-set! 1)
))
