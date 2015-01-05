(module Parse-test
   (library bkanren slib)
   (import (helpers "helpers.scm")
	   (loprog "loprog.sch")
	   (Parse "Parse.scm")
   ))

; (def-syntax λ lambda)
; (def-syntax + $+)
; (def-syntax - $-)
; (def-syntax * $*)
; (def-syntax / $/)

; (def-syntax conde tconde)
; (def-syntax == t==)
; (def-syntax run trun)
; (def-syntax run* trun*)

(pcg aa ([|.|] <=> 'a))
(pcg bb ([|.|] <=> 'a 'b))


(def [basic-tests]
(verify number (run* (q) (fresh (X) (number '(2 a 3) X q))) ===> 2)
(verify number (run* (q) (fresh (X) (number '(22 a 3) X q))) ===> 22)
;(verify number (run 3 (q) (fresh (X Y) (number `(,X a 3) Y q))) ===> 0 1 2)

(verify symbol (run* (q) (fresh (X) (symbol '(a 3) X q)))   ===> a)
(verify symbol (run* (q) (fresh (X) (symbol '(abc 3) X q)))   ===> abc)
;(verify symbol (run 3 (q) (fresh (X Y) (symbol `(,X 3) Y q)))   ===> a b c)

(verify literal (run* (q) (fresh (X) (literal '(2 ^ 3) X q))) ===> 2) 
(verify literal (run* (q) (fresh (X) (literal q X 4)))        ===> (4 . _.0))

(verify skipn (run* (q) (skipn 0 '(1 2) q)) ===> (1 2))
(verify skipn (run* (q) (skipn 1 '(1 2) q)) ===> (2))
(verify skipn (run* (q) (skipn 2 '(1 2) q)) ===> ())
(verify skipn (run* (q) (skipn 3 '(1 2) q)) =>) ; should fail

(verify unify (run* (q) (fresh (x) (== '((a 1) (a 1)) `(,x ,x)))) ===> _.0) 
(verify unify (run* (q) (fresh (x e) (== '((a 1) (a 1)) (cons x e))
	             (== e (cons x '()))
		     )) ===> _.0)
(verify unify (run* (q) (fresh (x e) (== '((a 1) (a 1)) `(,x . ,e))
	             (== e `(,x . ()))
		     )) ===> _.0)

(verify appendo (run* (q) (appendo q '(3) '(1 2 3))) ===> (1 2))
(verify appendo (run* (q) (appendo '(1 2) q '(1 2 3))) ===> (3))
(verify appendo (length (run* (q) (fresh (x y) (appendo x y '(1 2 3)) (== q `(result: ,x ,y))))) = 4)
(verify appendo (run* (q) (fresh (x y) (appendo '(1 2) x y) (== q `(result: ,x ,y)))) ===> (result: _.0 (1 2 . _.0)))
; appendo can handle non-ground [[x]] and [[y]]!
(verify appendo (run 2 (q) (fresh (x y) (appendo x '(3) y) (== q `(,x ,y)))) ---> (() (3)) ((_.0) (_.0 3)))

(verify aa1 (run* (q) (aa '(a) '() q)) ===> (a))
(verify aa2 (run* (q) (aa '(b) '() q)) =>)
(verify bb1 (run* (q) (bb '(a b) '() q)) ===> (a b))
(verify bb2 (run* (q) (bb '(b a) '() q)) =>)
)

; has to be PEG because of multi-result behavior
; Here we change left-recursion to right-recursion for the expression grammar
; associativity is a problem for ^ operator
; factor(pow(x,times(y . z))) --> literal(x), [^], factor(pow(y,times(.z).
(defn factor (pcg <= factor
(factor condo: condu ;locals: (x y z l)
 ; ; immediate divergence is prevented by <= and defn
 ([_ `(^ ,x ,y)] <=> (factor y) '^ (literal x))
 ; inductive case
 ([_ `(^ ,x (* . (,y . ,z)))] <=>
  (literal x) '^ (factor `(^ ,y (* . ,z)))) ; fix associativity
 ; ([_ `(^ ,x (* . ,l))]
 ;  <=[(== l `(,y . ,z))]=>
 ;  (literal x) '^ (factor `(^ ,y (* . ,z)))) ; fix associativity
 ; base case
 ([_ `(^ ,x (* ,y ,z))] <=> (literal x) '^ (factor `(^ ,y ,z)))         ; fix associativity
 ([_ `(^ ,x ,y)] <=> (literal x) '^ (factor y))
 ([_ x] <=> (literal x))
)))

(def [expr1-tests]
(verify factor (run* (q) (fresh (X) (factor '(2 a 3) X q))) ===> 2)
;
(verify factor (run* (q) (factor q '() '(^ 3 4))) ===> (3 ^ 4))
(verify factor (run* (q) (factor q '() '(^ 3 (* 4 5)))) ===> (3 ^ 4 ^ 5))
(verify factor (run* (q) (factor q '() '(^ 3 (* 4 5 6)))) ===> (3 ^ 4 ^ 5 ^ 6))
(verify factor (run* (q) (factor q '() '(^ 3 (* 4 5 6 7)))) ===> (3 ^ 4 ^ 5 ^ 6 ^ 7))
(verify factor (run* (q) (fresh (X) (factor q X '(^ 3 4)))) ===> ( 3 ^ 4 . _.0))
;
(verify factor (run* (q) (factor '(2 ^ 3) '() q)) ===> (^ 2 3))
(verify factor (run* (q) (fresh (X) (factor '(a ^ 1 ^ 3 5) X q))) ===> (^ a (* 1 3)))
(verify factor (run* (q) (fresh (X) (factor '(a ^ 1 ^ 3 ^ 5) X q))) ===> (^ a (* 1 3 5)))
(verify factor (run* (q) (fresh (X) (factor '(a ^ 1 ^ 3 ^ 5 ^ 7) X q)))  ===> (^ a (* 1 3 5 7)))
(verify factor (run* (q) (fresh (X) (factor '(p 3) X q))) ===> p)
(verify factor (run 0 (q) (fresh (x y) (factor x  '() y) (== q `(,x ,y)))) --->)
(verify factor-x (run 0 (q) (fresh (x y z) (factor x  y z) (== q `(,x ,y ,z)))) --->)
)


; some syntactic sugar

(pcg Ss
 ([S 'x] <=> ε)
 ([S 'x] <=> 'a 'a (Ss 'x))
)
(pcg S
 ([S 'x] <=> ε)
 ([S 'x] <=> (: 'a 'a (S 'x)))
)

(pcg A'
 ([] <=> ε)
 ;([A'] <=> 'a 'a)
 ([] <=> 'a [A'] 'a)
)

; context-free grammar aⁿbⁿ
; more on this later
(pcg A
 ([] <=> 'a ([A] ?) 'b)
)

(pcg B
 ([] <=> '< ('b *) '>)
)

(pcg BC0
 ([] <=> (('c / 'b / 'd) +))
)

(pcg BC
 ([] <=> '< (('c / 'b / 'd) +) '>)
)

(def [sugar-tests]
(verify S (run* (q) (S '() '() 'x)) ===> _.0)
(verify S (run* (q) (S '(b) '() 'x)) =>)
(verify S (run* (q) (S '(a) '() 'x)) =>)
(verify S (run* (q) (S '(a a) '() 'x)) ===> _.0)
(verify S (run 3 (q) (S q '() 'x)) ---> (a a a a) (a a) ()) 

(verify A' (run* (q) (A' '() '())) ===> _.0)
(verify A' (run* (q) (A' '(a a) '())) ===> _.0)
(verify A' (run* (q) (A' '(a a a a) '())) ===> _.0)
(verify A' (run 4 (q) (A' q '())) ---> (a a a a a a) (a a a a) (a a) ())

(verify A.fwd (run* (q) (A '() '())) =>)
(verify A.fwd (run* (q) (A '(a a) '())) =>)
(verify A.fwd (run* (q) (A '(b a) '())) =>)
(verify A.fwd (run* (q) (A '(a b) '())) ===> _.0)
(verify A.fwd (run* (q) (A '(a a b b) '())) ===> _.0)

; for some strange reason this doesn't work in Bigloo compiler (resulting binary diverges)
; for versions before 4.1a (22Jan14)
;(cond-expand (bigloo;-eval
(verify A.bwd (run 3 (q) (A q '())) ---> (a a b b) (a b) (a a a b b b))
;)(else))

(verify B (run* (q) (B '(< >) '())) ===> _.0)
(verify B (run* (q) (B '(< b >) '())) ===> _.0)
(verify B (run* (q) (B '(< b b >) '())) ===> _.0)
(verify B (run* (q) (B '(< b b b >) '())) ===> _.0)
(verify B (run 4 (q) (B q '())) ---> (< >) (< b >) (< b b >) (< b b b >))

(verify BC0 (run* (q) (BC0 '(< >) '())) =>)
(verify BC0 (run* (q) (BC0 '(d c a) '())) =>)
(verify BC0 (run* (q) (BC0 '(c) '())) ===> _.0)
(verify BC0 (run* (q) (BC0 '(c b) '())) ===> _.0)
(verify BC0 (run* (q) (BC0 '(d c c) '())) ===> _.0)
(verify BC0 (run 17 (q) (BC0 q '())) ---> (c) (b) (d) (c c) (c b) (c d) (b c) (d c) (c c c) (b b) (d b) (c c b) (b d) (d d) (c c d) (c b c) (c d c))


(verify BC (run* (q) (BC '(< >) '())) =>)
(verify BC (run* (q) (BC '(a) '())) =>)
(verify BC (run* (q) (BC '(< c >) '())) ===> _.0)
(verify BC (run* (q) (BC '(< c b >) '())) ===> _.0)
(verify BC (run* (q) (BC '(< d c c >) '())) ===> _.0)
(verify BC (run 17 (q) (BC q '())) ---> (< c >) (< b >) (< d >) (< c c >) (< c b >) (< c d >) (< b c >) (< d c >) (< c c c >) (< b b >) (< d b >) (< c c b >) (< b d >) (< d d >) (< c c d >) (< c b c >) (< c d c >))
)

; solving left-recursion by the "trick"
(pcg SS ;locals: (x)
 ([X 'z] <=> ε)
 ([_ `(S ,x)] <=> [SS x] 'a 'a)
)
;(def X [memo SS])
(def X SS)

; generate infinite stream of fresh variables
(def (freshº' x)
  (conde ([== x '()])
     (else (fresh (y z)
      (freshº z)
      (== x `(,y . ,z))
      ))
     ))
(def (prefixº' a b)
   (fresh (x)
      (freshº x)
      (appendo a x b)
      ;(appendo a `(fin . ,x) b)
      ))

(def freshº (predicate 
([_ '()])	     
([_ `(,y . ,z)] :-    
  (freshº z)	     
)))
(def prefixº (predicate locals: (x)
([_ a b] :- (freshº x) (appendo a x b))
))

(def [left-tests]
(verify SS.zero (run* (q) (X '() '() q)) ===> z)
(verify SS.fwd (run* (q) (X '(a a) '() q)) ===> (S z))
(verify SS.prefix (run* (q) (fresh (_ r) (X '(a a a a) _ r) (== q `(,_ ,r)))) ---> ((a a a a) z) ((a a) (S z)) (() (S (S z))))
(verify SS.fwd (run* (q) (X '(a a a a) '() q)) ===> (S (S z)))
(verify SS.fwd (run* (q) (X '(a a a a a a) '() q)) ===> (S (S (S z))))
(verify SS.rev0 (run* (q) (X q '() 'z)) ===> ())
(verify SS.rev1 (run* (q) (X q '() '(S z))) ===> (a a))
(verify SS.rev2 (run* (q) (X q '() '(S (S z)))) ===> (a a a a))
(verify SS.fail (run* (q) (X '(a) '() q)) =>)
(verify SS.fail (run* (q) (X '(a a a) '() q)) =>)
(verify SS.fail (run* (q) (X '(a a a a a) '() q)) =>)
(verify SS.fail (run* (q) (X q '() 'x)) =>)
(verify SS.fail (run* (q) (X q '() '(S x))) =>)
(verify SS.fail (run* (q) (X q '() '(S (S x)))) =>)
(verify SS.enum (run 3 (q) (fresh (x y) (X x '() y) (== q `(,x ,y)))) ---> (() z) ((a a) (S z)) ((a a a a) (S (S z))))

(verify freshº (run 4 (q) (freshº q)) ---> (_.0 _.1 _.2) (_.0 _.1) (_.0) ())

(verify prefixº (run 4 (q) (prefixº '(1 2 3) q)) ---> (1 2 3) (1 2 3 _.0) (1 2 3 _.0 _.1) (1 2 3 _.0 _.1 _.2))
;(verify prefixº (run 4 (q) (prefixº '(1 2 3) q)) ---> (1 2 3 fin) (1 2 3 fin _.0) (1 2 3 fin _.0 _.1) (1 2 3 fin _.0 _.1 _.2))

(verify X (run 1 (q) (fresh (l _) (prefixº '() l) (X l `(fin . ,_) q))) ===> z)
(verify X (run 1 (q) (fresh (l _) (prefixº '(a a) l) (X l `(fin . ,_) q))) ===> (S z))
(verify X (run 1 (q) (fresh (l _) (prefixº '(a a a a) l) (X l `(fin . ,_) q))) ===> (S (S z)))
(verify X (run 1 (q) (fresh (l _) (prefixº '(a a a a a a) l) (X l `(fin . ,_) q))) ===> (S (S (S z))))

; since we append an infinite suffix of fresh vars, we can get as many S's as we need
(verify SS (run 3 (q) (fresh (l) (prefixº '() l) (X l `() q))) ---> z (S z) (S (S z)))
(verify SS (run 2 (q) (fresh (l) (prefixº '(a a) l) (X l `() q))) ---> (S (S z)) (S z))
(verify SS (run 2 (q) (fresh (l) (prefixº '(a a a a) l) (X l `() q))) ---> (S (S (S z))) (S (S z)))
(verify SS (run 2 (q) (fresh (l) (prefixº '(a a a a a a) l) (X l `() q))) ---> (S (S (S (S z)))) (S (S (S z))))

;the whole output must be known before recreating the input
;(verify X (run 1 (q) (fresh (l _) (prefixº '(z) l) (X q `(fin . ,_) l))) ===> ())

;(exit)
)

; Hutton's razor with exponents
; left-factoring, complete, but not reversible since the bottom is never reached
; can not use full inference here because of inherited "attributes", e.g., [[x]]
;(def (factor . args) #u)
	      
(defn exprs (pcg <=> expr
(factor locals: (x)
 ;([_ `(,x . ,z)] <=> [literal x] [factor' '() z])
 ([_ y] <=> ;do[(trace-vars 'exprs (x y))] ; can not trace Lin/Lout because of hygiene
	[literal x] [factor' x y])
)
(factor' locals: (y)
 ([_ x z] <=> ;do[(trace-vars 'exprs (x y z))]
	  '^ [literal y] [factor' `(^ ,x ,y) z])
 ([_ x x] <=> ε)
 ;([_ x y] <=[(== x y)]=> ε)
)
(term locals: (x)
 ([_ y] <=> ;do[(trace-vars 'exprs (x y))]
	[factor x] [term' x y])
)
(term' locals: (y)
 ([_ x z] <=> ;do[(trace-vars 'exprs (x y z))]
	  '* [factor y] [term' `(* ,x ,y) z])
 ([_ x z] <=> ;do[(trace-vars 'exprs (x y z))]
	  '/ [factor y] [term' `(/ ,x ,y) z])
 ([_ x x] <=> ε)
)
(expr locals: (x)
 ([_ y] <=> ;do[(trace-vars 'exprs (x y))]
	[term x] [expr' x y])
)
(expr' locals: (y)
 ([_ x z] <=> ;do[(trace-vars 'exprs (x y z))]
	  '+ [term y] [expr' `(+ ,x ,y) z])
 ([_ x z] <=> ;do[(trace-vars 'exprs (x y z))]
	  '- [term y] [expr' `(- ,x ,y) z])
 ([_ x x] <=> ε)
)
))

(def [right-tests]
(verify exprs.factor (run* (q) (exprs '(2) '() q)) ===> 2)
;(verify exprs (run* (q) (exprs q '() '())) =>)
(verify exprs.factor (run* (q) (exprs '(2 ^ 3) '() q)) ===> (^ 2 3))
;(verify exprs (run* (q) (exprs q '() '(^ 2 3))) ===> (2 ^ 3))
(verify exprs.factor (run* (q) (exprs '(2 ^ 3 ^ 5) '() q)) ===> (^ (^ 2 3) 5))
;
(verify exprs.term (run* (q) (exprs '(2) '() q)) ===> 2)
; ;(verify exprs (run* (q) (exprs q '() '())) =>)
(verify exprs.term (run* (q) (exprs '(2 * 3) '() q)) ===> (* 2 3))
; ;(verify exprs (run* (q) (exprs q '() '(^ 2 3))) ===> (2 ^ 3))
(verify exprs.term (run* (q) (exprs '(2 * 3 * 5) '() q)) ===> (* (* 2 3) 5))
; ;
(verify exprs.expr (run* (q) (exprs '(2) '() q)) ===> 2)
; ;(verify exprs (run* (q) (exprs q '() '())) =>)
(verify exprs.expr (run* (q) (exprs '(2 + 3) '() q)) ===> (+ 2 3))
; ;(verify exprs (run* (q) (exprs q '() '(^ 2 3))) ===> (2 ^ 3))
(verify exprs.expr (run* (q) (exprs '(2 + 3 + 5) '() q)) ===> (+ (+ 2 3) 5))
(verify exprs.expr (run* (q) (exprs '(2 + 3 + :xx) '() q)) =>)
(verify exprs.expr (run* (q) (fresh (x) (exprs '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))
(verify exprs.expr (run* (q) (fresh (x) (exprs '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
;(verify exprs.expr (run 1 (q) (fresh (x) (exprs q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))
)


; Correct associativity for operators,
; no need to do left-recursion elimination
; still need to do separation into sub-goals to solve precedence
; Need to put the base case at the end because of
; potential immediate mutual infinite descent

; non-encapsulated version for better testing
; defaults to bidirectional, complete
(pcg
(Factor ;locals: (x y)
 ([_ `(^ ,x ,y)] <=> [Factor x] '^ [literal y])
 ;([_ `(begin ,x)] <=> `(,[Expr x]))
 ([_ x] <=> [literal x])
)
(Term ;locals: (x y)
 ([_ `(* ,x ,y)] <=> [Term x] '* [Factor y])
 ([_ `(/ ,x ,y)] <=> [Term x] '/ [Factor y])
 ([_ x] <=> [Factor x])
)
(Expr ;locals: (x y)
 ([_ `(+ ,x ,y)] <=> [Expr x] '+ [Term y])
 ([_ `(- ,x ,y)] <=> [Expr x] '- [Term y])
 ([_ x] <=> [Term x])
))

(def [good-tests]
(verify Factor (run* (q) (fresh (X) (Factor '(2 a 3) X q))) ===> 2)
;
(verify Factor (run* (q) (Factor '(2 ^ 3) '() q)) ===> (^ 2 3))
(verify Factor (run* (q) (Factor '(a ^ 1 ^ 3 5) '(5) q)) ===> (^ (^ a 1) 3))
(verify Factor (run* (q) (Factor '(a ^ 1 ^ 3 ^ 5) '() q)) ===> (^ (^ (^ a 1) 3) 5))
(verify Factor (run* (q) (Factor '(a ^ 1 ^ 3 ^ 5 ^ 7) '() q))  ===> (^ (^ (^ (^ a 1) 3) 5) 7))
(verify Factor (run* (q) (fresh (X) (Factor '(p 3) X q))) ===> p)
;
(verify Factor (run* (q) (Factor q '() '(^ 3 4))) ===> (3 ^ 4))
(verify Factor (run* (q) (Factor q '() '(^ (^ 3 4) 5))) ===> (3 ^ 4 ^ 5))
(verify Factor (run* (q) (Factor q '() '(^ (^ (^ 3 4) 5) 6))) ===> (3 ^ 4 ^ 5 ^ 6))
(verify Factor (run* (q) (Factor q '() '(^ (^ (^ (^ 3 4) 5) 6) 7))) ===> (3 ^ 4 ^ 5 ^ 6 ^ 7))
(verify Factor1 (run* (q) (fresh (X) (Factor q X '(^ 3 4)))) ===> ( 3 ^ 4 . _.0))

(verify Factor (run* (q) (Factor q '() '(^ (^ 3 4) (^ 5 6)))) =>)

(verify Term (run* (q) (fresh (x) (Term '(1 * 3) '() q))) ===> (* 1 3))
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5 * 7) '() q))) ===> (* (* (* 1 3) 5) 7)) 
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5 * 7 * 9) '() q))) ===> (* (* (* (* 1 3) 5) 7) 9))

(verify Term (run* (q) (fresh (x) (Term '(1 * 3 ^ 5) '() q))) ===> (* 1 (^ 3 5)))
(verify Term (run* (q) (fresh (x) (Term '(1 ^ 3 * 5) '() q))) ===> (* (^ 1 3) 5))

(verify Term1 (run* (q) (fresh (x) (Term q '() '(* (* 1 3) 5)))) ===> (1 * 3 * 5))
(verify Term (run* (q) (fresh (x) (Term q '() '(* (* (* 1 3) 5) 7)))) ===> (1 * 3 * 5 * 7))
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 3 5)))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 (* 3 5))))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 (* 3 (* 5 7)))))) =>) ; should fail
;(exit)

(verify Term (run* (q) (fresh (x) (Term '(1 / 3 / 5) '() q))) ===> (/ (/ 1 3) 5))
(verify Term2 (run* (q) (fresh (x) (Term '(1 / 3 / 5 / 7) '() q))) ===> (/ (/ (/ 1 3) 5) 7))
(verify Term (run* (q) (fresh (x) (Term '(1 / 3 / 5 / 7 / 9) '() q))) ===> (/ (/ (/ (/ 1 3) 5) 7) 9))

(verify Term (run* (q) (fresh (x) (Term q '() '(/ 1 3 5)))) =>) ; should fail
(verify Term3 (run* (q) (fresh (x) (Term q '() '(/ 1 (/ 3 5))))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(/ 1 (/ 3 (/ 5 7)))))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(/ (/ 1 3) 5)))) ===> (1 / 3 / 5))
(verify Term (run* (q) (fresh (x) (Term q '() '(/ (/ (/ 1 3) 5) 7)))) ===> (1 / 3 / 5 / 7))

(verify Term-todo1 (run* (q) (fresh (x) (Term '(1 * 3 / 5) '() q))) ===> (/ (* 1 3) 5))
(verify Term-todo1 (run* (q) (fresh (x) (Term q '() '(* 1 (/ 3 5))))) =>) ; should fail
(verify Term-todo1 (run* (q) (fresh (x) (Term q '() '(/ (* 1 3) 5)))) ===> (1 * 3 / 5))

(verify Term-todo2 (run* (q) (fresh (x) (Term '(1 / 3 * 5) '() q))) ===> (* (/ 1 3) 5))
(verify Term-todo2 (run* (q) (fresh (x) (Term q '() '(/ 1 (* 3 5))))) =>) ; should fail
(verify Term-todo2 (run* (q) (fresh (x) (Term q '() '(* (/ 1 3) 5)))) ===> (1 / 3 * 5))
;
(verify Term (run* (q) (fresh (x) (Term q '() '2))) ===> (2))
;(exit)

(verify Expr (run* (q) (fresh (x) (Expr '(1 + 3) '() q))) ===> (+ 1 3))
(verify Expr (run* (q) (fresh (x) (Expr '(1 + 3 + 5) '() q))) ===> (+ (+ 1 3) 5))
(verify Expr (run* (q) (fresh (x) (Expr '(1 * 3 + 5) '() q))) ===> (+ (* 1 3) 5))
(verify Expr (run* (q) (fresh (x) (Expr '(1 + 3 * 5) '() q))) ===> (+ 1 (* 3 5)))
(verify Expr (run* (q) (fresh (x) (Expr '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify Expr (run* (q) (fresh (x) (Expr '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
(verify Expr (run* (q) (fresh (x) (Expr '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))

(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ 1 3)))) ===> (1 + 3))
(verify Expr1 (run* (q) (fresh (x) (Expr q '() '(+ (+ 1 3) 5)))) ===> (1 + 3 + 5))
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ 1 (+ 3 5))))) =>)
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ (* 2 1) (* 3 5))))) ===> (2 * 1 + 3 * 5))
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))

(verify Expr (run* (q) (fresh (x) (Expr '(3) '() q))) ===> 3)

(verify Expr (last-pair (run 6 (q)
		(fresh (l _)
		   (prefixº '(1 * 2 + 3 * 5) l)
		   (Expr l _  q)))) ===> (+ (* 1 2) (* 3 5)))
)

(defn ife (pcg <=> if
(if condo: condu;locals: (x y z)
 ([_ `(if ,x ,y ,z)] <=> 'if [Expr x] 'then [Expr y] 'else [Expr z])
 ([_ `(if ,x ,y #f)] <=> 'if [Expr x] 'then [Expr y])
 ([_ `(if ,x ,y ,z)] <=> 'if [Expr x] 'then [if y] 'else [Expr z])
 ([_ `(if ,x ,y #f)] <=> 'if [Expr x] 'then [if y])
)))

(def [ife-tests]
(verify ife.ex1 (run* (q) (ife '(
if 1
then 2
else 3
) '() q)) ===> (if 1 2 3))

(verify ife.ex2 (run* (q) (ife '(
if 1 * 2 + 3
then x + 9 * y
else a - b - c
) '() q)) ===> (if (+ (* 1 2) 3) (+ x (* 9 y)) (- (- a b) c)))

(verify ife.else (run* (q) (ife '(if 1 then 2) '() q)) ===> (if 1 2 #false))
(verify ife.nest (run* (q) (ife '(if 1 then if 2 then 3 else 4 else 5) '() q)) ===> (if 1 (if 2 3 4) 5))
(verify ife.dangling (run* (q) (ife '(if 1 then if 2 then 3 else 4) '() q)) ===> (if 1 (if 2 3 4) #false))
(verify ife.cut (run* (q) (ife '(if 1 then if 2 then 3) '() q)) ===> (if 1 (if 2 3 #false) #false))
(verify ife.rev (run* (q) (ife q '() '(if 1 2 3))) ===> (if 1 then 2 else 3))
(verify ife.rev (run* (q) (ife q '() '(if 1 2 #f))) ===> (if 1 then 2))
(verify ife.rev (run* (q) (ife q '() '(if 1 (if 2 3 4) #f))) ===> (if 1 then if 2 then 3 else 4))
(verify ife.rev (run* (q) (ife q '() '(if 1 (if 2 3 #f) #f))) ===> (if 1 then if 2 then 3))
(verify ife.rev (run* (q) (ife q '() '(if 1 (if 2 3 4) 5))) ===> (if 1 then if 2 then 3 else 4 else 5))
)

; encapsulate internal goals
; bidirectional, complete (halts on no parse) and no sideways
(defn hutton (pcg <=> Expr
(Factor ;locals: (x y)
 ([_ `(^ ,x ,y)] <=> [Factor x] '^ [literal y])
 ; have to keep the structure in place!!
 ;([_ `(,x)] <=> '< (Expr x) '>)
 ; as we keep the structure, lets keep SOS in place
 ([_ `(begin ,x)] <=> `(,[Expr x]))
 ; can not use these since the structure of the parenths would be gone!
 ; can not collapse multiple states as that would lead to infinite regress
 ; when running backwards and hence incomplete (also leading to failures in
 ; reversibility of[[ifo.rev]] rules below)
 ;([_ x] <=> `(,(Expr x)))
 ;([_ x] <=> '< (Expr x) '>)
 
 ([_ x] <=> [literal x])
)
(Term ;locals: (x y)
 ([_ `(* ,x ,y)] <=> [Term x] '* [Factor y])
 ([_ `(/ ,x ,y)] <=> [Term x] '/ [Factor y])
 ([_ x] <=> [Factor x])
)
(Expr ;locals: (x y)
 ([_ `(+ ,x ,y)] <=> [Expr x] '+ [Term y])
 ([_ `(- ,x ,y)] <=> [Expr x] '- [Term y])
 ([_ x] <=> [Term x])
)))

(def [hutton-tests]
(verify hutton (run* (q) (fresh (x) (hutton '(3) '() q))) ===> 3)
(verify hutton (run* (q) (fresh (x) (hutton '(1 + 3) '() q))) ===> (+ 1 3))
(verify hutton (run* (q) (fresh (x) (hutton '(1 + 3 + 5) '() q))) ===> (+ (+ 1 3) 5))
(verify hutton (run* (q) (fresh (x) (hutton '(1 + (3 + 5)) '() q))) ===> (+ 1 (begin (+ 3 5))))
(verify hutton (run* (q) (fresh (x) (hutton '(1 * 3 + 5) '() q))) ===> (+ (* 1 3) 5))
(verify hutton (run* (q) (hutton '(1 * 3 + 5) '() '(+ (* 1 3) 5))) ===> _.0)
(verify hutton (run* (q) (fresh (x) (hutton '(1 + 3 * 5) '() q))) ===> (+ 1 (* 3 5)))
(verify hutton (run* (q) (fresh (x) (hutton '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify hutton (run* (q) (fresh (x) (hutton '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
(verify hutton (run* (q) (fresh (x) (hutton '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))

(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ 1 3)))) ===> (1 + 3))
(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ (+ 1 3) 5)))) ===> (1 + 3 + 5))
(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ 1 (begin (+ 3 5)))))) ===> (1 + (3 + 5)))
(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ 1 (let () (+ 3 5)))))) =>)
(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ (* 2 1) (* 3 5))))) ===> (2 * 1 + 3 * 5))
(verify hutton (run* (q) (fresh (x) (hutton q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))
)

(defn ifo (pcg <=> if
(if condo: condu;locals: (x y z)
 ([_ `(if ,x ,y ,z)] <=> 'if [hutton x] 'then [hutton y] 'else [hutton z])
 ([_ `(if ,x ,y #f)] <=> 'if [hutton x] 'then [hutton y])
 ([_ `(if ,x ,y ,z)] <=> 'if [hutton x] 'then [if y] 'else [hutton z])
 ([_ `(if ,x ,y #f)] <=> 'if [hutton x] 'then [if y])
)))

(def [ifo-tests]
(verify ifo.ex1 (run* (q) (ifo '(
if 1
then 2
else 3
) '() q)) ===> (if 1 2 3))

(verify ifo.ex2 (run* (q) (ifo '(
if 1 * 2 + 3
then x + 9 * y
else a - b - c
) '() q)) ===> (if (+ (* 1 2) 3) (+ x (* 9 y)) (- (- a b) c)))

(verify ifo.ex3 (run* (q) (ifo '(
if 1 * (2 + 3)
then (x + 9 * y)
else a - (b - c)
) '() q)) ===> (if (* 1 (begin (+ 2 3))) (begin (+ x (* 9 y))) (- a (begin (- b c)))))

(verify ifo.else (run* (q) (ifo '(if 1 then 2) '() q)) ===> (if 1 2 #false))
(verify ifo.nest (run* (q) (ifo '(if 1 then if 2 then 3 else 4 else 5) '() q)) ===> (if 1 (if 2 3 4) 5))
(verify ifo.dangling (run* (q) (ifo '(if 1 then if 2 then 3 else 4) '() q)) ===> (if 1 (if 2 3 4) #false))
(verify ifo.cut (run* (q) (ifo '(if 1 then if 2 then 3) '() q)) ===> (if 1 (if 2 3 #false) #false))
(verify ifo.rev (run* (q) (ifo q '() '(if 1 2 3))) ===> (if 1 then 2 else 3))
(verify ifo.rev (run* (q) (ifo q '() '(if 1 2 #f))) ===> (if 1 then 2))
(verify ifo.rev (run* (q) (ifo q '() '(if 1 (if 2 3 4) #f))) ===> (if 1 then if 2 then 3 else 4))
(verify ifo.rev (run* (q) (ifo q '() '(if 1 (if 2 3 #f) #f))) ===> (if 1 then if 2 then 3))
(verify ifo.rev (run* (q) (ifo q '() '(if 1 (if 2 3 4) 5))) ===> (if 1 then if 2 then 3 else 4 else 5))
)

; add sideways, starts to lean left, so incomplete (diverges on no parse), but can generate all pairs
(def hutton' (pcg => Expr
(Factor ;locals: (x y)
 ([_ `(^ ,x ,y)] <=> [Factor x] '^ [literal y])
 ([_ `(begin ,x)] <=> `(,[Expr x]))
 ([_ x] <=> [literal x])
)
(Term ;locals: (x y)
 ([_ `(* ,x ,y)] <=> [Term x] '* [Factor y])
 ([_ `(/ ,x ,y)] <=> [Term x] '/ [Factor y])
 ([_ x] <=> [Factor x])
)
(Expr ;locals: (x y)
 ([_ `(+ ,x ,y)] <=> [Expr x] '+ [Term y])
 ([_ `(- ,x ,y)] <=> [Expr x] '- [Term y])
 ([_ x] <=> [Term x])
)))

(def [hutton'-tests]
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(3) '() q))) ===> 3)
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 + 3) '() q))) ===> (+ 1 3))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 + 3 + 5) '() q))) ===> (+ (+ 1 3) 5))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 + (3 + 5)) '() q))) ===> (+ 1 (begin (+ 3 5))))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 * 3 + 5) '() q))) ===> (+ (* 1 3) 5))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 + 3 * 5) '() q))) ===> (+ 1 (* 3 5)))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
(verify hutton'.f (run* (q) (fresh (x) (hutton' '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))

; we use run(1) here because [[hutton']] is incomplete
(verify hutton'.b (run 1 (q) (fresh (x) (hutton' q '() '(+ 1 3)))) ===> (1 + 3))
(verify hutton'.b (run 1 (q) (fresh (x) (hutton' q '() '(+ (+ 1 3) 5)))) ===> (1 + 3 + 5))
(verify hutton'.b (run 1 (q) (fresh (x) (hutton' q '() '(+ 1 (begin (+ 3 5)))))) ===> (1 + (3 + 5)))
;incomplete!
;(verify hutton' (run 1 (q) (fresh (x) (hutton' q '() '(+ 1 (let () (+ 3 5)))))) ===> (1 + (3 + 5)))
(verify hutton'.b (run 1 (q) (fresh (x) (hutton' q '() '(+ (* 2 1) (* 3 5))))) ===> (2 * 1 + 3 * 5))
(verify hutton'.b (run 1 (q) (fresh (x) (hutton' q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))

;;this is the price we pay for handling bidirectionality in a nice way (run*, not run(N))
(verify hutton'.s1 (run 10 (q) (fresh (x y) (hutton' x  '()  y) (== q `(,x ,y)))) --->
(((_.0) _.0) (sym _.0))
(((_.0) _.0) (num _.0))
(((_.0 + _.1) (+ _.0 _.1)) (sym _.0 _.1))
(((_.0 + _.1) (+ _.0 _.1)) (num _.0) (sym _.1))
(((_.0 * _.1) (* _.0 _.1)) (sym _.0 _.1))
(((_.0 * _.1) (* _.0 _.1)) (num _.0) (sym _.1))
(((_.0 + _.1) (+ _.0 _.1)) (num _.1) (sym _.0))
(((_.0 + _.1) (+ _.0 _.1)) (num _.0 _.1))
(((_.0 ^ _.1) (^ _.0 _.1)) (sym _.0 _.1))
((((_.0) + _.1) (+ (begin _.0) _.1)) (sym _.0 _.1))
; (((_.0) _.0) (sym _.0))
; (((_.0) _.0) (num _.0))
; (((_.0 + _.1) (+ _.0 _.1)) (sym _.0 _.1))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.0) (sym _.1))
; (((_.0 * _.1) (* _.0 _.1)) (sym _.0 _.1))
; (((_.0 * _.1) (* _.0 _.1)) (num _.0) (sym _.1))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.1) (sym _.0))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.0 _.1))
; (((_.0 ^ _.1) (^ _.0 _.1)) (sym _.0 _.1))
; (((_.0 ^ _.1) (^ _.0 _.1)) (num _.0) (sym _.1))
)

;;this is the price we pay for handling bidirectionality in a nice way (run*, not run(N))
(verify hutton'.s2
(run 10 (q) (fresh (x y) (hutton' x  '()  y) (== q `(,x ,y)))) --->
(((_.0) _.0) (sym _.0))
(((_.0) _.0) (num _.0))
(((_.0 + _.1) (+ _.0 _.1)) (sym _.0 _.1))
(((_.0 + _.1) (+ _.0 _.1)) (num _.0) (sym _.1))
(((_.0 * _.1) (* _.0 _.1)) (sym _.0 _.1))
(((_.0 * _.1) (* _.0 _.1)) (num _.0) (sym _.1))
(((_.0 + _.1) (+ _.0 _.1)) (num _.1) (sym _.0))
(((_.0 + _.1) (+ _.0 _.1)) (num _.0 _.1))
(((_.0 ^ _.1) (^ _.0 _.1)) (sym _.0 _.1))
((((_.0) + _.1) (+ (begin _.0) _.1)) (sym _.0 _.1))
; (((_.0) _.0) (sym _.0))
; (((_.0) _.0) (num _.0))
; (((_.0 + _.1) (+ _.0 _.1)) (sym _.0 _.1))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.0) (sym _.1))
; (((_.0 * _.1) (* _.0 _.1)) (sym _.0 _.1))
; (((_.0 * _.1) (* _.0 _.1)) (num _.0) (sym _.1))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.1) (sym _.0))
; (((_.0 + _.1) (+ _.0 _.1)) (num _.0 _.1))
; (((_.0 ^ _.1) (^ _.0 _.1)) (sym _.0 _.1))
; (((_.0 ^ _.1) (^ _.0 _.1)) (num _.0) (sym _.1))
))

; immediate infinite self-recursion
(pcg BB ;locals: (b)
   ([_ `(B ,b)] <=> [BB b])
)

; example from [[http://okmij.org/ftp/Haskell/LeftRecursion.hs]]
; S -> S A C | C
; A -> B | aCa
; B -> B
; C -> b | C A
(defn gram (pcg => S
(S ([_ `(S ,s ,a ,c)] <=> ;do[(begin (write 'S0) #s)]
		       [S s] [A a] [C c])
   ([_ `(S ,c)] <=> ;do[(begin (write 'S1) #s)]
		[C c]))
(A ([_ `(A ,b)] <=> ;do[(begin (write 'A0) #s)]
		[B b])
   ([_ `(A a ,c a)] <=> ;do[(begin (write 'A1) #s)]
		    'a [C c] 'a))
(B ([_ `(B ,b)] <=> ;do[(begin (write 'B) #s)]
		[B b]))
(C ([_ `(C b)] <=> ;do[(begin (write 'C0) #s)]
	       'b)
   ([_ `(C ,c ,a)] <=> ;do[(begin (write 'C1) #s)]
		   [C c] [A a]))
))


; a grammar from Mercury paper, we know left-recursion won't hurt,
; so for [[a]] and [[d]] we inhibit collapse to FAIL by prepending a matcher with ε
(defn merc (pcg <=> a
 (a ([_ `(a ,x)] <=> ε ([b x] / [c x])))
 (b ([_ `(b ,x)] <=> 'x [d x] 'y))
 (c ([_ `(c ,x)] <=> 'x [d x] 'z))
 (d ([_ `(d ,x)] <=> ε ([a x] / ε)))
 ))

(def [gram-tests]
(verify gram (run* (q) (gram '(a b a b) '() q)) =>)
(verify gram (run* (q) (gram q '() '())) =>)
(verify gram (run* (q) (gram '(b a b a b) '() q)) ===> (S (S (C b)) (A a (C b) a) (C b)))
;incomplete!
;(verify gram (run* (q) (gram q '() '(S (S (C b)) (A a (C b) a) (C b)))) ===> (b a b a b))
(verify gram (run 1 (q) (gram q '() '(S (S (C b)) (A a (C b) a) (C b)))) ===> (b a b a b))
(verify gram (run* (q) (gram '(b a b a b a b a) '() q)) ===> (S (S (C b)) (A a (C b) a) (C (C b) (A a (C b) a))))
;incomplete!
;(verify gram (run* (q) (gram q '() '(S (S (C b)) (A a (C b) a) (C (C b) (A a (C b) a))))) ===> (b a b a b a b a))
(verify gram (run 1 (q) (gram q '() '(S (S (C b)) (A a (C b) a) (C (C b) (A a (C b) a))))) ===> (b a b a b a b a))
;;this is the price we pay for handling bidirectionality in a nice way (run*, not run(N))
(verify gram (run 7 (q) (fresh (x y) (gram x '() y) (== q x))) --->
(b) (b a b a) (b a b a b) (b a b a b a b a) (b a b a b a a) (b a b a a b a) (b a b a b a b a b a a))


(verify merc (run* (q) (merc '(x x x z z z) '() q)) ---> (a (c (d (a (c (d (a (c (d _.0))))))))))
)

;; nested parsers (explicit version)
(pcg N ;locals: (x)
   ([_] <=> 'x)
   ([_ `(N ,x)] <=> '< (N x) '>))

;; testing un-quasiquote
(pcg P ;locals: (x)
   ([_] <=> 'x)
   ([_ `(P ,x)] <=> ;do[(trace-vars 'p (x))]
		`(a ,(P x) b) 'E))

;; nested parsers (piggybacking on Scheme's reader)
(pcg PP ;locals: (x)
   ([_] <=> 'x)
   ([_ `(PP ,x)] <=> `(,[PP x]))
)

(pcg Q ;locals: (x)
   ([_] <=> 'x)
   ([_ `(Q1 ,x)] <=> `(a ,[Q x] `b))
   ([_ `(Q2 ,x)] <=> `(c ,`(d ,[Q x] 'e) f))
   ([_ `(Q3 ,x)] <=> `(g ,`(,[Q x]) h))
   ;XXX TODO([_ `(Q ,x)] <=> `(a `(b ,,(Q x) c) d) 'E) 
)

(def [nested-tests]
(verify N.fail (run* (q) (N '() '() q)) =>)
(verify N.sing (run* (q) (N '(x) '() q)) ===> x)
(verify N.wrap (run* (q) (N '(< x >) '() q)) ===> (N x))
(verify N.dwra (run* (q) (N '(< < x > >) '() q)) ===> (N (N x)))
(verify N.rev.fail (run* (q) (N q '() '())) =>)
(verify N.rev.sing (run* (q) (N q '() 'x)) ===> (x))
(verify N.rev.wrap (run* (q) (N q '() '(N x))) ===> (< x >))
(verify N.rev.drwap (run* (q) (N q '() '(N (N x)))) ===> (< < x > >))
(verify N.enum (run 5 (q) (fresh (x y) (N x '() y) (== q x))) ---> (x) (< x >) (< < x > >) (< < < x > > > ) (< < < < x > > > > ))

(verify P (run* (q) (P '((a b) E) '() q)) =>)
(verify P (run* (q) (P q '() '())) =>)
(verify P (run* (q) (P '((a x b) E) '() q)) ===> (P x))
(verify P (run* (q) (P q '() '(P x))) ===> ((a x b) E))
(verify P (run* (q) (P '((a (a x b) E b) E) '() q)) ===> (P (P x)))
(verify P (run* (q) (P q '() '(P (P x)))) ===> ((a (a x b) E b) E))
(verify P (run 5 (q) (fresh (x y) (P x '() y) (== q y))) ---> x (P x) (P (P x)) (P (P (P x))) (P (P (P (P x)))))

(verify PP (run* (q) (PP '() '() q)) =>)
(verify PP (run* (q) (PP q '() '())) =>)
(verify PP (run* (q) (PP '(x) '() q)) ===> x)
(verify PP (run* (q) (PP q '() 'x)) ===> (x))
(verify PP (run* (q) (PP '([x]) '() q)) ===> (PP x))
(verify PP (run* (q) (PP q '() '(PP x))) ===> ([x]))
(verify PP (run* (q) (PP '([[x]]) '() q)) ===> (PP (PP x)))
(verify PP (run* (q) (PP q '() '(PP (PP x)))) ===> ([[x]]))
(verify PP (run 5 (q) (fresh (x y) (PP x '() y) (== q x))) ---> (x) ((x)) (((x))) ((((x)))) (((((x))))))


(verify Q (run* (q) (Q '() '() q)) =>)
(verify Q (run* (q) (Q '((a b)) '() q)) =>)
(verify Q (run* (q) (Q q '() '())) =>)
(verify Q (run* (q) (Q '((a x b)) '() q)) ===> (Q1 x))
(verify Q (run* (q) (Q q '() '(Q1 x))) ===> ((a x b)))
(verify Q (run* (q) (Q '((c (d x e) f)) '() q)) ===> (Q2 x))
(verify Q (run* (q) (Q q '() '(Q2 x))) ===> ((c (d x e) f)))
(verify Q (run* (q) (Q '((c (d (a x b) e) f)) '() q)) ===> (Q2 (Q1 x)))
(verify Q (run* (q) (Q q '() '(Q2 (Q1 x)))) ===> ((c (d (a x b) e) f)))
(verify Q (run* (q) (Q '((g ((a x b)) h)) '() q)) ===> (Q3 (Q1 x)))
(verify Q (run* (q) (Q q '() '(Q3 (Q1 x)))) ===> ((g ((a x b)) h)))
(verify Q (run* (q) (Q '((g (x) h)) '() q)) ===> (Q3 x))
(verify Q (run* (q) (Q q '() '(Q3 x))) ===> ((g (x) h)))
(verify Q (run 10 (q) (fresh (x y) (Q x '() y) (== q y))) ---> x (Q1 x) (Q2 x) (Q1 (Q1 x)) (Q3 x) (Q1 (Q2 x)) (Q2 (Q1 x)) (Q1 (Q1 (Q1 x))) (Q3 (Q1 x)) (Q1 (Q3 x)))
)

; S -> x S x | x should not work for Packrat (according to Wikipedia). Still,
; it is context free.
; maybe a hint that our formalism is not strictly PEG (i.e., linear time),
; but more general type-1 (i.e., exponential) e.g., CYK,
; or even type-0 (turing-complete). Most likely, type-0 since its equivalent
; to attribute grammars
(defn s (pcg <=> S
 (S
   ([_] <=> 'x)
   ([_ `(s ,x)] <=> 'x [S x] 'x)
   )
)) 

; reversible aⁿbⁿ (we can count!)
; the _ automatically ensures that we only use vars declared in the head,
; i.e., if used in the body then it must be declared in the head
(defn anbn (pcg <=> a
 (a ([_ `(S ,x)] <=> 'a ([a x] ?) 'b))
 ))

; non context-free grammar aⁿbⁿcⁿ
; S ← &(A 'c') 'a'+ B !('a'/'b'/'c')
; A ← 'a' A? 'b'
; B ← 'b' B? 'c'
(defn aⁿbⁿcⁿ (pcg <=> S
  (S ([] <=> when([A] 'c) ('a +) [B] unless(['a / 'b / 'c])))
  (A ([] <=> 'a ([A] ?) 'b))
  (B ([] <=> 'b ([B] ?) 'c))
  ))

(defn aⁿbⁿaⁿ (pcg <=> S
  (S ([] <=> when([A] 'a) ('a +) [B] unless(['a / 'b])))
  (A ([] <=> 'a ([A] ?) 'b))
  (B ([] <=> 'b ([B] ?) 'a))
  ))


(def [levels-tests]
(verify s (run* (q) (s '() '() q)) =>)
(verify s (run* (q) (s '(y) '() q)) =>)
(verify s (run* (q) (s '(x) '() q)) ===> x)
(verify s (run* (q) (s '(x x x) '() q)) ===> (s x))
(verify s (run* (q) (s q '() '())) =>)
(verify s (run* (q) (s q '() 'y)) =>)
(verify s (run* (q) (s q '() 'x)) ===> (x))
(verify s (run* (q) (s q '() '(s x))) ===> (x x x))

(verify s.enum (run 3 (q) (fresh (x y) (s x '() y) (== q x))) ---> (x) (x x x) (x x x x x))

(verify anbn.empty (run* (q) (anbn '() '() q))=>)
(verify anbn.fail (run* (q) (anbn '(a) '() q))=>)
(verify anbn.fail (run* (q) (anbn '(b) '() q))=>)
(verify anbn.empty (run* (q) (anbn q '() '()))=>)
(verify anbn.1 (run* (q) (anbn '(a b) '() q))===>(S _.0))
(verify anbn.1.rev (run* (q) (anbn q '() '(S x)))===>(a b))
(verify anbn.1.rev (run* (q) (anbn q '() '(S y)))===>(a b))
(verify anbn.2 (run* (q) (anbn '(a a b b) '() q))===>(S (S _.0)))
; x can be unified with (S x), hence double result
(verify anbn.2.rev (run* (q) (anbn q '() '(S (S x))))--->(a b) (a a b b))
;(verify anbn.enum (run 2 (q) (fresh (x y) (anbn x '() y) (== q x)))--->(a b) (a a b b))

(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '() '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a b c) '())) ===> _.0)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b b c c) '())) ===> _.0)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b b c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b c c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a b b c c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a a b b b c c c) '())) ===> _.0)
;(cond-expand (bigloo;-eval
(verify aⁿbⁿcⁿ (run 3 (q) (aⁿbⁿcⁿ q '())) ---> (a b c . _.0) (a a b b c c . _.0) (a a a b b b c c c . _.0))
;)(else))
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '() '())) =>)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a b a) '())) ===> _.0)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a a b b a a) '())) ===> _.0)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a a b b a) '())) =>)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a a b a a) '())) =>)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a b b a a) '())) =>)
(verify aⁿbⁿaⁿ (run* (q) (aⁿbⁿaⁿ '(a a a b b b a a a) '())) ===> _.0)
;(cond-expand (bigloo;-eval
(verify aⁿbⁿaⁿ (run 3 (q) (aⁿbⁿaⁿ q '())) ---> (a b a . _.0) (a a b b a a . _.0) (a a a b b b a a a . _.0))
;)(else))
)

; higher-order rules
(defn [comma p] (pcg <=> c
 (c ([_ `(,x . ,y)] <=>
		    [c y]
		    ;[(comma p) y] ;using def and this would lead to immediate runaway recursion
		    'comma
		    [p x]
		    ;'comma
		    ;[(comma p) y] ;OK for forward, diverges on backward
		    ;[c y]
		    )
    ([_ `(,x)] <=> [p x])
  )
 ))
(pcg a ([_] <=> 'a))
(pcg b ([_] <=> 'b))

(def [hofs-tests]
(verify comma (run* (q) ([comma a] '() '() q)) =>)
(verify comma (run* (q) ([comma a] '(b) '() q)) =>)
(verify comma.rev (run* (q) ([comma a] q '() '())) =>)
(verify comma (run* (q) ([comma a] '(a) '() q)) ===> (a))
(verify comma.rev (run 1 (q) ([comma a] q '() '(a))) ===> (a))
(verify comma (run* (q) ([comma b] '() '() q)) =>)
(verify comma (run* (q) ([comma b] '(b) '() q)) ===> (b))
(verify comma (run* (q) ([comma b] '(a) '() q)) =>)

(verify comma (run* (q) ([comma a] '(comma a) '() q)) =>)
(verify comma (run* (q) ([comma a] '(b comma a) '() q)) =>)
(verify comma (run* (q) ([comma a] '(a comma a) '() q)) ===> (a a))
(verify comma.rev (run 1 (q) ([comma a] q '() '(a a))) ===> (a comma a))
(verify comma (run* (q) ([comma b] '(comma b) '() q)) =>)
(verify comma (run* (q) ([comma b] '(b comma b) '() q)) ===> (b b))
;(verify comma.rev (run 1 (q) ([comma a] q '() '(b b))) =>)
(verify comma (run* (q) ([comma b] '(a comma b) '() q)) =>)

(verify comma (run 3 (q) (fresh (x y) ([comma a] x '() y) (== q y))) ---> (a) (a a) (a a a))
)

(pcg ;<=> Expr
(Factor'
 ([_ (proj (λ (z) (y (if (null? z) x `(^ ,z ,x)))))] <=> [literal x] '^ [Factor' y])
 ;([_ `(begin ,x)] <=> `(,[Expr x]))
 ([_ (proj (λ (z) (if (null? z) x `(^ ,z ,x))))] <=> [literal x])
)
; (Term'
;  ([_ (proj (λ (z) (y (if (null? z) x `(* ,z ,x)))))] <=> [Factor' x] '* [Term' y])
;  ([_ (proj (λ (z) (y (if (null? z) x `(/ ,z ,x)))))] <=> [Factor' x] '/ [Term' y])
;  ([_ (proj (λ (z) (if (null? z) x `(* ,z ,x))))] <=> [Factor' x])
; )
; (Expr
;  ([_ `(+ ,x ,y)] <=> [Term x] '+ [Expr y])
;  ([_ `(- ,x ,y)] <=> [Term x] '- [Expr y])
;  ([_ x] <=> [Term x])
; )
)

(pcg m
 ([_ 'z (quote z)] <=> ε)
 ;([_ `(m ,x)] <=> 'x [m x])
 ;([_ `(m ,x) 'M] <=> 'x [m x])
 ;([_ (proj (list 'm x))] <=> 'x [m x])
 ;([_ `(m ,x) π(list 'M y)] <=> 'x [m x y])
 ([_  π(list 'M x) `(m ,y)] <=> 'x [m x y])
 )

(def [proj-tests]
(verify Factor' ([first (run* (q) (fresh (X) (Factor' '(2 a 3) X q)))] '()) === 2)
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3) '() q))] '()) === '(^ 2 3))
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3 ^ 4) '() q))] '()) === '(^ (^ 2 3) 4))
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3 ^ 4 ^ 5) '() q))] '()) === '(^ (^ (^ 2 3) 4) 5))
;(verify Factor' ([(first (run* (q) (Term' '(2 ^ 3) '() q))) '()] '()) === '(^ 2 3))
;(verify Factor ([(first (run* (q) (Term '(2 * 3) '() q))) '()] '()) === '(* 2 3))
(verify m (run* (q) (fresh (a b) (m 'x '() a b) (== q `(,a ,b)))) =>)
(verify m (run* (q) (fresh (a b) (m '() '() a b) (== q `(,a ,b)))) ===> (z z))
(verify m (run* (q) (fresh (a b) (m '(x) '() a b) (== q `(,a ,b)))) ===> ((M z) (m z)))
(verify m (run* (q) (fresh (a b) (m '(x x) '() a b) (== q `(,a ,b)))) ===> ((M (M z)) (m (m z))))
)


(pcg	      
(lev0
 ([_ π x] <=> [literal x])
 ([_ π x] <=> `(,[lev3 x]))
)
(lev1
 ([_ π(^ x y)] <=> [lev1 x] '^ [lev0 y])
 ([_ π x] <=> [lev0 x]) 
)
(lev2 extend: extend
 ([_ π(* x y)] <=> [lev2 x] '* [lev1 y])
 ;([_ π(/ x y)] <=> [lev2 x] '/ [lev1 y])
 ([_ π x] <=> [lev1 x])
)
(lev3 extend: extend
 ([_ π(+ x y)] <=> [lev3 x] '+ [lev2 y])
 ;([_ π(- x y)] <=> [lev3 x] '- [lev2 y])
 ([_ π x] <=> [lev2 x])
)
(Eval ([_ π x] <=> ε [lev3 x]))
);)

(def lev2-/ (let ([extend' (extend)][lev2' lev2])
  (fn-with [apply extend'] || 'lev2 =>
     ;(pp 'here)
     ; need to η-expand the rule because of parameterize
     ;(λ args  ;(pp 'there)
       ; explicit lifting needed to prevent runaway left-recursion
       ;(define lev2
	  (pcg ([_ π(/ x y)] <=> [lift lev2' x] '/ [lev1 y]))
	  ;)
       ; prevent infinite regress
       ;(parameterize ([extend *def-extend*])
	  ;(apply lev2 args)
       ;))
	  )
  ))

(def lev3-- (let ([extend' lev2-/];(extend)]
		  [lev3' lev3])
  (fn-with [apply extend'] || 'lev3 => ;(pp 'here)
     ; need to η-expand the rule because of parameterize
     ;(λ args ;(pp 'there)
       ; explicit lifting needed to prevent runaway left-recursion
       ;(define lev3
     (pcg ([_ π(- x y)] <=> [lift lev3' x] '- [lev2 y]))
     ;)
       ; prevent infinite regress
       ;(parameterize ([extend *def-extend*])
	;  (apply lev3 args)
        ;))
	  )
  ))

(def [extend-tests]
(verify Eval (run* (q) (Eval '(2 ^ 3) '() q)) ===> 8)
(verify Eval (run* (q) (Eval '(2 ^ 3 ^ 2) '() q)) ===> 64)
(verify Eval (run* (q) (Eval '(2 ^ (3 * 2)) '() q)) ===> 64)
(verify Eval (run* (q) (Eval '(2 ^ (3 ^ 2)) '() q)) ===> 512)
(verify Eval (run* (q) (Eval '(2 * 3 * 4) '() q)) ===> 24)
(verify Eval (run* (q) (Eval '(2 + 3 + 4) '() q)) ===> 9)
(verify Eval (run* (q) (Eval '(2 + 3 * 4) '() q)) ===> 14)
(verify Eval (run* (q) (Eval '(2 * 3 + 4) '() q)) ===> 10)
(verify Eval (run* (q) (Eval '(2 * (3 + 4)) '() q)) ===> 14)
(verify Eval (run* (q) (Eval '(2 * 3 + 4 * 5) '() q)) ===> 26)

(parameterize ([extend lev2-/])
(verify Eval.ext1 (run* (q) (Eval '(4 / 2) '() q)) ===> 2)
(verify Eval.ext2 (run* (q) (Eval '(4 * 3 / 2) '() q)) ===> 6)
(verify Eval.ext2' (run* (q) (Eval '(4 / 2 * 3) '() q)) ===> 6)
(verify Eval.ext2' (run* (q) (Eval '(8 / 2 / 2) '() q)) ===> 2)
)

(extend lev3--)

;(parameterize ([extend lev3--])
(verify Eval.ext3 (run* (q) (Eval '(4 * 3 - 2) '() q)) ===> 10)
(verify Eval.ext1' (run* (q) (Eval '(4 / 2) '() q)) ===> 2)
(verify Eval.ext2' (run* (q) (Eval '(4 * 3 / 2) '() q)) ===> 6)
(verify Eval.ext4 (run* (q) (Eval '(3 - 4 / 2) '() q)) ===> 1)
(verify Eval.ext5 (run* (q) (Eval '(4 / 2 - 1) '() q)) ===> 1)
;)
)

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
; ([_ `([,n . ,va] . ,ar) `([,n . ,vb] . ,br)] :-
;  ((== va vb) /
;   (== 'xxx vb))
;  (test ar br))
([_ `([,n1 . ,va] . ,ar) `([,n2 . ,vb] . ,br)] :-
 ([(== va vb) : (== n1 n2)] /
  [(== 'xxx vb) : (== n1 n2)])
 (test ar br))
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
   (pp (run 1 (q) (bar '(s x s y s z s b s c s d) '() q)))
   (pp (run 0 (q) (bar q '() '(((x y z b c d))))))
   (pp (run 0 (q) (foo q '() '(((x y z) (b c d))))))
   )


(cond-expand (bigloo-eval
	      (basic-tests)
	      (expr1-tests)
	      (sugar-tests)
	      (left-tests)
	      (right-tests)
	      (good-tests)
	      (ife-tests)
	      (hutton-tests)
	      (ifo-tests)
	      (hutton'-tests)
	      (gram-tests)
	      (nested-tests)
	      (levels-tests)
	      (hofs-tests)
	      (proj-tests)
	      (extend-tests)
	      (char-tests)
	      (pred-tests)
	      (foo-tests)
	      ))
