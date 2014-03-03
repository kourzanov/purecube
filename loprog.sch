; beginning
(module loprog
   (import ascript synrules)
   (export take-from nullᵒ?  pairᵒ? carᵒ cdrᵒ consᵒ !))
;(load "synrules.sch")
; some syntactic sugar
(set-sharp-read-syntax! 's succeed)
(set-sharp-read-syntax! 'u fail)
(define-syntax ≡ ==)

(define-syntax-rule [except pred args ...]
   (project (args ...)
	(if [pred args ...]
	    #u
	    #s)))

(define-syntax-rule [trace-vars name (id* ...)]
   (lambda (s)
       (pp (list name (reify id* s) ...))
       (succeed s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; relational list operations
(define (nullᵒ? x) [≡ x '()])
(define (pairᵒ? x) (fresh (x0 x1) [≡ x `(,x0 . ,x1)]))
(define (carᵒ x y) (fresh (t) [≡ x `(,y . ,t)]))
(define (cdrᵒ x y) (fresh (h) [≡ x `(,h . ,y)]))
(define (consᵒ h t l) (≡ l `(,h . ,t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (! p . args)
   (condu
      ((apply p args) #u)
      (else #s)))

(define (!2 p a b)
   (condu
      ((p a b) #u)
      ((p b a) #u)      
      (else #s)))

(define (notᵒ f) (lambda args
  (apply ! `(,f . ,args))))

(define (!ᵒ2 f) (lambda (a b)
  (!2 f a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define take-from
   (λ () _ => #u
    ¦ `(,head . ,tail) f =>
      (conde
       ([≡ f head])
       (else (take-from tail f)))
    ¦ db _ => (error 'take-from "bad database" db)))

(define (memberᵒ e l)
  (conde
    ([nullᵒ? l] #u)
    (else (fresh (h t)
      ;(all
	 (≡ l `(,h . ,t))
	 (conde
	  ([≡ e h])
	  (else (memberᵒ e t)))))))

(define (insertᵒ e l r)
  (conde
    ([≡ r `(,e . ,l)])
    (else (fresh (h t sr)
       ;(all
	 (≡ l `(,h . ,t))
	 (≡ r `(,h . ,sr))
	 (insertᵒ e t sr)
	 ))))

(define (subsetᵒ s l)
   (conde
      ((nullᵒ? l) (nullᵒ? s))
      (else (fresh (e s' l') 
	  (consᵒ e l' l)
	  ;(trace-vars 'subset (e l'))
	  (subsetᵒ s' l')
	  (conde
	     ((≡ s `(,e . ,s')))
	     ((≡ s s'))
	 )))
      ))
; the end