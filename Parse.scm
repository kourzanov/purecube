(module Parse
   (library bkanren slib)
   (import (helpers "helpers.scm")
	   (loprog "loprog.sch"))
   (export number symbol strings not-strings
	   literal skipn appendo extend
	   idem chars= chars syms=)
   )

(def-syntax λ lambda)
(def-syntax ∘ compose)

; (def-syntax conde tconde)
; (def-syntax == t==)
; (def-syntax run trun)
; (def-syntax run* trun*)

; (def-syntax ≡ t==)̧
; (defn (nullo? x) [≡ x '()])
; (defn (pairo? x) (fresh (x0 x1) [≡ x `(,x0 . ,x1)]))
; (defn (caro x y) (fresh (t) [≡ x `(,y . ,t)]))
; (defn (cdro x y) (fresh (h) [≡ x `(,h . ,y)]))
; (defn (conso h t l) (≡ l `(,h . ,t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn (number Lin Lout x)
  (all
   (numbero x)
   (conso x Lout Lin)
   ))

(defn (symbol Lin Lout x)
  (all
   (symbolo x)
   (conso x Lout Lin)
   ))

(defn (not-strings Lin Lout x)
   (conde
      ((symbolo x) (conso x Lout Lin))
      ((numbero x) (conso x Lout Lin))
   ))

(defn (strings Lin Lout x)
  (all
   (stringo x)
   (conso x Lout Lin)
   ))

; literal --> symbol.
; literal --> number.
(defn (literal Lin Lout x)
   (conde
      ([symbol Lin Lout x])
      ([number Lin Lout x])
      ;([strings Lin Lout x])
      ))

(def (skipn n a b)
   (if [> n 0]
       (fresh (_ c)
	  (== a `(,_ . ,c))
	  (skipn (- n 1) c b))
       (== a b)))

;(def (idem Lin Lout v) (consᵒ v Lout Lin))
(defn idem (curry (∘ [uncurry consᵒ] reverse)))
(defn (swallow Lin Lout _) (== Lin Lout))

(defn (chars Lin Lout sym x)
 (all
   (appendo (string->list (symbol->string sym)) Lout Lin)
   (== x sym)
   ))
(defn (chars= Lin Lout sym)
   (appendo (string->list (symbol->string sym)) Lout Lin)
   )
(defn (syms= Lin Lout sym)
   (appendo (map (compose string->symbol string) (string->list (symbol->string sym))) Lout Lin)
   )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-syntax revs (syntax-rules ()
       ([_ () () . r] r)
       ([_ (k args ...) () . r] (k args ... . r))
       ([_ k (h . t) . r] (revs k t h . r))
       ))

(def-syntax (scheme-bindings (k a b [s ...] . d))
   (k a b [s ... list first second pair? car cdr null? if cond begin
                 + - * / ^ = == : |,|
                 list->string string->integer integer->ucs2 char->integer
                 string->symbol] . d))

(def-syntax revv (syntax-rules ()
       ([_ () r] r)
       ([_ (k args ...) r] (k args ... . r))
       ([_ k r h . t] (revv k t h . r))
       ))
(def-syntax zip2 (syntax-rules … ()
	([_ (k …) () () . a] (k … . a))
	([_ k (x . xs) (y . ys) . a] (zip2 k xs ys (x y) . a))
	 ))
(def-syntax zip3 (syntax-rules … ()
	([_ (k …) () () () . a] (k … . a))
	([_ k (x . xs) (y . ys) (z . zs) . a] (zip3 k xs ys zs (x y z) . a))
	 ))
(def-syntax zip4 (syntax-rules … ()
	([_ (k …) () () () () . a] (k … . a))
	([_ k (x . xs) (y . ys) (z . zs) (w . ws) . a] (zip4 k xs ys zs ws (x y z w) . a))
	 ))

(def-syntax member?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (id . ids) xs kt kf] kf)
      ([_ id (x . r) kt kf]
       (let-syntax ([test (syntax-rules (id)
			     ([_ id t f] t)
			     ([_ xx t f] f))])
	  (test x kt (member?? id r kt kf))
	  ))))

;; new style
(def-syntax [hd (k ...) a . _] (k ... a))
(def-syntax [tl (k ...) _ . a] (k ... . a))
(def-syntax nth (syntax-rules ()
 ([_ k (1) . l] (hd k . l))
 ([_ k (1 . rest) . l] (tl (nth k rest) . l))
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-syntax make-scope (syntax-rules (project)
       ([_ _ _ _] #s) ; is this really needed here? YES, for safety
       ([_ _ () head . body] (head . body))
       ; DONE: check that vars are grounded
       ([_ project (var ...) _ . body]
	(project (var ...)
	   (or (and (ground? var) ... . body) #s)
	))
       ([_ fresh vars _ . body] (fresh vars . body))
       ))

(def-syntax qs (syntax-rules .. (qq quote unquote quasiquote unquote-splicing) 
     ; this strips one level of quoting
     ([_ q        (k ..)   () . a]   (k .. . a))
     ; only do one level quasi-quote
     ([_ []       k `y . a]   (qs [qq] k y . a))
     ([_ q        k `y . a]   (qs    q k () 'y . a))
     ; only do one level unquote
     ; trigger on ,` to pass control back to [[seq]] below
     ([_ [qq]     k ,`y . a]  (qs [] k () [qq y] . a))
     ([_ [qq]     k ,y  . a]  (qs [] k () y . a))
     ([_ []       k ,y . a]   (bad-unquote k ,y))
     ; quote just stays quote
     ([_ q        k 'y . a]   (qs q k () 'y . a))
     ; process lists, this is the most important form over here!
     ([_ [qq]     k (y . ys) . a] (qs [qq] (qs [qq] k y) ys . a))
     ; has to be quote!
     ([_ [qq . q] k  y . a]   (qs  q k 'y . a))
     ))
  
(def-syntax w (syntax-rules .. (qq quote unquote quasiquote unquote-splicing
 		       lambda λ let let* letrec do project
		       )
     ; the end is nearer...
     ([_ q   (k ..) b [] . a]  (k .. . a))
     ; quasi-quote
     ([_ q        k b `t . a]  (w [qq . q] k b t . a)) ; do vars only
     ([_ [qq . q] k b ,t . a]  (w q k b t . a))
     ([_ []       k b ,t . a]  (bad-unquote k b ,t))
     ; quote just stays quote
     ([_ q        k b 't . a]  (w q k b [] . a)) ; do vars only
     ; process known forms that do binding
     ; introduce [[end]] at the beginning since the lists are processed outside-in
     ; save the current set of bindings in [[a]] on top of the stack, and restore upon
     ; processing the [[end]]. accumulated set of local bindings is forgotten
     ; the scoping rules below ensure that free bindings are replicated to both the [[save]]
     ; and the accumulated set, which is the only set used for checking the membership
     ([_ []  k b [lambda (var ..) . body] . a]            (w [] k (var .. . b) body                   . a))
     ([_ []  k b [λ (var ..) . body] . a]                 (w [] k (var .. . b) body                   . a))
     ([_ []  k b [project (var ..) . body] . a]           (w [] k b            body                   . a))
     ([_ []  k b [let ([var val] ..) . body] . a]         (w [] k (var .. . b) [val .. . body]        . a))
     ([_ []  k b [let* ([var val] ..) . body] . a]        (w [] k (var .. . b) [val .. . body]        . a))
     ([_ []  k b [letrec ([var val] ..) . body] . a]      (w [] k (var .. . b) [val .. . body]        . a))
     ([_ []  k b [let loop ([var val] ..) . body] . a]    (w [] k (var .. . b) [val .. . body]        . a))
     ([_ []  k b [do ([var . val] ..) fender . body] . a] (w [] k (var .. . b) [val .. fender . body] . a))
     ; process lists, this is the most important form over here!
     ([_ q  k b [t . ts] . a] (w q (w q k b t) b ts . a))
     ; scoping
     ; check if this a free binding (symbol)
     ; do vars only
     ([_ [] k b t a ..]
      (symbol?? t
     	 (member?? t (a .. . b)
     	    (w [] k b [] a ..)
     	    (w [] k b [] a .. t))
     	    (w [] k b [] a ..)
	    ))
     ; quoted things are skipped over
     ([_ [qq . q] k b t . a]   (w q k b [] . a))
     ))

(def-syntax proc-/ (syntax-rules (/)
  ([_ in out c (k ...) heads] (k ... #u)) ; is this really needed here? YES, for safety
  ([_ in out c (k ...) heads a] (k ... [(seq in out c () () heads a)]))
  ([_ in out c (k ...) heads a / . as] (proc-/ in out c (k ... [(seq in out c () () heads a)]) heads . as))
))

(def-syntax seq
   (syntax-rules (qq quote unquote quasiquote unquote-splicing
		  do ε when unless skip ? + * / : lift unlift)
                  ;rev: ref: reb: reu:)
      ; [[in]] is the input list
      ; [[out]] is the output list
      ; [[c]] is the non-determinism engine (conde, condu)
      ; [[acc]] accumulates constituents of a rule
      ; [[temps]] accumulates fresh/temporary variables in a rule (threading the difference list)
      ; [[heads]]=[heads ac] contains information on the set of mutually-recursive [[heads]]
      ;  and the [[ac]] contains preceding sets of rules in this head
      ; the rest is the list of constituents to parse
      ;
      ; avoid introducing unnecessary temporary by handling last rules separately (short-circuit in-out)
      ([_ in out _ acc temps heads do(actions ...)]     (revs (make-scope fresh temps all) (actions ... . acc)))
      ; delegate this both to ^^^
      ([_ in out c acc temps heads ε]             (seq in out c acc temps heads do[(== in out)]))
      ; XXX TODO remove this? (its not reversible)
      ; since this is the last rule, no further [[clashes]] for temp can ensue
      ; and we don't need to generate a new temporary
      ([_ in out c acc temps heads (skip n)]      (seq in out c acc temps heads do[(skipn n in out)]))
      ([_ in out c acc temps heads skip]          (seq in out c acc temps heads do[(fresh (hole) (== in `(,hole . ,out)))]))
      ; quoted terminals
      ([_ in out c acc temps heads (quote datum)]
       (seq in out c acc temps heads do[(== in `(datum . ,out))]
      ))
      ([_ in out c acc temps [heads (ac ...)] `datum]
       (let ([data #false]) ; just to generate a new temporary
	  (seq in out c acc (data . temps) [heads (ac ... . acc)]
	     ; actions are in reverse
	     do[(qs [] (seq data '() c () () [heads (ac ... . acc)]) `datum)
                (== in `(,data . ,out))
                ])
	  ))
      ([_ in out c acc temps [heads (ac ...)] (: goals ...)]
       (seq in out c acc temps [heads (ac ...)] 
	  do[(all (seq in out c () () [heads (ac ... . acc)] goals ...))]
       ))
      ([_ in out c acc temps [heads (ac ...)] (goals ... ?)]
       (seq in out c acc temps [heads (ac ...)]
	  do[(c ((seq in out c () () [heads (ac ... . acc)] goals ...))
		((== in out)))]
       ))
      ([_ in out c acc temps [heads (ac ...)] (alt / . alts)]
        (seq in out c acc temps heads do[(proc-/ in out c (c) [heads (ac ... . acc)] alt / . alts)]
       ))
      ;; [[*]] combinator that collects functor arguments for all [[goals]] into
      ;; lists as it iterates on the input
      ;; does it nest? YES, it does
      ([_ in out c acc temps heads (goals ... *)]
       (seq in out c acc temps heads (goals ... * #false #false)))
      ([_ in out c acc temps heads (goals ... +)]
       (seq in out c acc temps heads (goals ... * 1 #false)))
      ([_ in out c acc temps heads (goals ... + lower upper)]
       (seq in out c acc temps heads (goals ... * lower upper)))
      ([_ in out c acc temps [(r . heads) (ac ...)] (goals ... * lower upper)]
      (let-syntax ([K (syntax-rules .. ()
       ; we need to explicitly get the [[in]] and [[out]] from the caller
       ([_ in out vars ..] ; 1st bunch
	(let loop ([count 0][lin in][lout out] [vars '()] ..)
	(let-syntax ([K (syntax-rules … ()
	([_ res …] ; 2nd bunch
	  (let ([res #false] …)
	  (make-scope fresh (res …) begin
	   (letrec-syntax ([K (syntax-rules .... ()
	   ([_ gls (v v1 v2 v3) ....]
	    ; and now declare the 3rd bunch of vars
	    ; and substitute it for the original var in [[gls]]==[[goals]]
	    (cond ([and upper (>= count upper)]
             (all [== lin lout]
		  (== v1 v) ....))
	     ([and lower (< count lower)]
	       (let ([temp #false][v3 #false] ....)
		(fresh (temp v3 ....)
		   ; rename original var to a local temporary
		   (let-syntax ([v v3] ....)
		      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
		      )
		   (appendo v1 `(,v3) v2) ....
		   [loop (+ count 1) temp lout v2 ....])
		))
	     (else (c ([== lin lout]
		(== v1 v) ....)
	       ((let ([temp #false][v3 #false] ....)
		(fresh (temp v3 ....)
		   ; rename original var to a local temporary
		   (let-syntax ([v v3] ....)
		      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
		      )
		   (appendo v1 `(,v3) v2) ....
		   [loop (+ count 1) temp lout v2 ....])
		))
		)))
             ))]
	    [K1 (syntax-rules ()
	     ([_ var gls . args]
	      ; zip all the vars together
	      (zip4 (K gls) var . args)
	      ))]
	    [K0 (syntax-rules ()
	     ([_ . vs] ; 3rd bunch
	      ; extract the 4rd bunch of free-vars
	      ; now with the same colour as in [[goals]]
	      (extract* vs (goals ...)
		 (K1 [] (goals ...) (vars ..) (res …) vs)
	      )))])
	      ; retrieve the 3rd bunch of free-vars
	      (scheme-bindings (w [] (K0) heads (goals ...)))
	      ))))
	)])
	   ; retrieve the 2nd bunch of free-vars
	   (scheme-bindings (w [] (K) heads (goals ...)))
	)))
       )])
       ; retrieve the 1st bunch of free-vars
       ; we need to pass [[in]] and [[out]] as they would
       ; otherwise be renamed
       (seq in out c acc temps [(r . heads) (ac ...)]
	  do[(scheme-bindings (w [] (K in out) heads (goals ...)))])
       ))
      
      ;; XXX TODO not really needed anymore: can emulate by playing with
      ;; [[lower]] and [[upper]]... see above
      
      ;; [[+]] combinator that collects functor arguments for all [[goals]] into
      ;; lists as it iterates on the input
      ([_ in out c acc temps heads (goals ... +)]
       (seq in out c acc temps heads (goals ... + #false #false)))
      ([_ in out c acc temps [(r . heads) (ac ...)] (goals ... + lower upper)]
      (let-syntax ([K (syntax-rules .. ()
       ; we need to explicitly get the [[in]] and [[out]] from the caller
       ([_ in out vars ..] ; 1st bunch
	(let loop ([count 0][lin in][lout out] [vars '()] ..)
	(let-syntax ([K (syntax-rules … ()
	([_ res …] ; 2nd bunch
	  (let ([res #false] …)
	  (make-scope fresh (res …) begin
	   (letrec-syntax ([K (syntax-rules .... ()
	   ([_ gls (v v1 v2 v3) ....]
	    ; and now declare the 3rd bunch of vars
	    ; and substitute it for the original var in [[gls]]==[[goals]]
	    (cond ([and upper (>= count upper)]
             (all [== temp lout]
		  (appendo v1 `(,v3) v) ....))
	     ([and lower (< count lower)]
	     (let ([temp #false][v3 #false] ....)
	     (fresh (temp v3 ....)
	      ; rename original var to a local temporary
	      (let-syntax ([v v3] ....)
	      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
	      )
	      (all
		 (appendo v1 `(,v3) v2) ....
		 [loop (+ count 1) temp lout v2 ....])
	      )))
	     (else (let ([temp #false][v3 #false] ....)
	     (fresh (temp v3 ....)
	      ; rename original var to a local temporary
	      (let-syntax ([v v3] ....)
	      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
	      )
	      (c ([== temp lout]
		  (appendo v1 `(,v3) v) ....)
		 ((appendo v1 `(,v3) v2) ....
		  [loop (+ count 1) temp lout v2 ....])
	      ))))
             )))]
	    [K1 (syntax-rules ()
	     ([_ var gls . args]
	      ; zip all the vars together
	      (zip4 (K gls) var . args)
	      ))]
	    [K0 (syntax-rules ()
	     ([_ . vs] ; 3rd bunch
	      ; extract the 4rd bunch of free-vars
	      ; now with the same colour as in [[goals]]
	      (extract* vs (goals ...)
		 (K1 [] (goals ...) (vars ..) (res …) vs)
	      )))])
	      ; retrieve the 3rd bunch of free-vars
	      (scheme-bindings (w [] (K0) heads (goals ...)))
	      )))
	  )
	)])
	   ; retrieve the 2nd bunch of free-vars
	   (scheme-bindings (w [] (K) heads (goals ...)))
	)))
       )])
       ; retrieve the 1st bunch of free-vars
       ; we need to pass [[in]] and [[out]] as they would
       ; otherwise be renamed
       (seq in out c acc temps [(r . heads) (ac ...)]
	  do[(scheme-bindings (w [] (K in out) heads (goals ...)))])
       ))
      ;<=: support, we know left-recursion won't hurt
      ([_ in out c () temps [(reu: . heads) ()] (lift goal . args)] (seq in out c () temps [(reu: . heads) ()] do[(goal in out . args)]))
      ;don't need to muck around with the tail-recursive call (if it is the only one, no way to avoid bottom)
      ([_ in out c () temps [(x . heads) ()] (lift goal . args)] (seq in out c () temps [(x . heads) ()] do[#u (== in out)]))
      ([_ in out c acc temps heads (lift goal . args)] (seq in out c acc temps heads do[(goal in out . args)]))
      ;tie the knot (or tie the belt), and then do the call recursively
      ([_ in out c acc temps heads (unlift goal . args)] (seq in out c acc temps heads do[(goal . args) (== in out)]))
      ; auto-lift the [[goal]] if found in [[heads]], only if this is the only sub-goal in the first rule of a goal
      ([_ in out c () temps [(r . heads) ()] (goal . args)]
       (member?? goal heads
      	  (seq in out c () temps [(r . heads) ()] (lift goal . args))
      	  (seq in out c () temps [(r . heads) ()] do[(goal in out . args)])
      	  ))
      ; regular goal - no need to generate temporaries
      ([_ in out c acc temps heads (goal . args)]
       (seq in out c acc temps heads do[(goal in out . args)]))
      ;; predicates
      ([_ in out c acc temps [heads (ac ...)] when guards]
	  (seq in out c acc temps [heads (ac ...)] 
	     do[(fresh (temp) (c ((seq in temp c () () [heads (ac ... . acc)] . guards) #s) (else #u)))]
	     ))
      ([_ in out c acc temps [heads (ac ...)] unless guards]
	  (seq in out c acc temps [heads (ac ...)] 
	     do[(fresh (temp) (c ((seq in temp c () () [heads (ac ... . acc)] . guards) #u) (else #s)))]
	     ))
      ; XXX this rule has to be last in this group
      ; auto-quote other terminals
      ([_ in out c acc temps heads datum]
       (seq in out c acc temps heads do[(== in `(datum . ,out))]
      ))
      ;; TODO: delegate processing for all sub-patterns, just like for [[+]] and [[*]]
      ; collect all actions and rules in the [[acc]]
      ([_ in out c acc temps heads do(actions ...) . rest] (seq in out c (actions ... . acc) temps heads . rest))
      ;; THIS IS WRONG
      ;([_ in out c acc temps heads ε . rest]         (seq in out c ([== in out] . acc) temps heads . rest))
      ;; TODO: THIS IS BETTER, BUT CAN BE IMPROVED (i.e., elided)
      ([_ in out c acc temps heads ε . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([== in temp]
			 . acc)
	     (temp . temps) heads . rest)
       )
       )
      ; XXX TODO remove this? (its not reversible)
      ([_ in out c acc temps heads (skip n) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([skipn n in temp]
			 . acc)
	     (temp . temps) heads . rest)
       )
       )
      ([_ in out c acc temps heads skip . rest]
       (let ([temp #false][hole #false]) ; just to generate new temporaries
	  ; temp is propagated, along with [[hole]] for efficiency
	  (seq temp out c ([== in `(,hole . ,temp)]
			 . acc)
	     (temp hole . temps) heads . rest)
       )
       )
      ; quoted terminals
      ([_ in out c acc temps heads (quote datum) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([== in `(datum . ,temp)]
			 . acc)
	     (temp . temps) heads . rest)
       )
       )
      ; [[qs]] generates [[qq]] rather than quasi-quote. we have to re-map it here back to quasi-quote
      ([_ in out c acc temps heads (qq datum) . rest] (seq in out c acc temps heads `datum . rest))
      ([_ in out c acc temps [heads (ac ...)] `datum . rest]
       (let ([temp #false][data #false]) ; just to generate new temporaries
	  (seq temp out c ((qs [] (seq data '() c () () [heads (ac ... . acc)]) `datum)
			   [== in `(,data . ,temp)]
			 . acc)
	     (temp data . temps) [heads (ac ...)] . rest)
	  )
      )
      ([_ in out c acc temps [heads (ac ...)] (: goals ...) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ((all (seq in temp c () () [heads (ac ... . acc)] goals ...))
			 . acc)
	     (temp . temps) [heads (ac ...)] . rest)
       )
      )
      ; nested [[seq]] invocations that reset the acc, need to have
      ; it propagated via [[heads]] for correct auto-lifting
      ([_ in out c acc temps [heads (ac ...)] (goals ... ?) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ((c ((seq in temp c () () [heads (ac ... . acc)] goals ...))
			      ((== in temp)))
			 . acc)
	     (temp . temps) [heads (ac ...)] . rest)
       )
      )
      ([_ in out c acc temps [heads (ac ...)] (alt / . alts) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([proc-/ in temp c (c) [heads (ac ... . acc)] alt / . alts]
			 . acc)
	     (temp . temps) heads . rest)
       )
      )
      ;; delegate processing to the handler for [[*]] above
      ([_ in out c acc temps [heads (ac ...)] (goals ... *) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([seq in temp c () () [heads (ac ... . acc)] (goals ... *)]
			   . acc)
	     (temp . temps) [heads (ac ...)] . rest)
       )
      )
      ;; delegate processing to the handler for [[+]] above
      ([_ in out c acc temps [heads (ac ...)] (goals ... +) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([seq in temp c () () [heads (ac ... . acc)] (goals ... +)]
			   . acc)
	     (temp . temps) [heads (ac ...)] . rest)
       )
      )
      ; accumulate recursive calls in the tail (tie the knot and the belt in the last recursive call, see above)
      ([_ in out c acc temps heads (unlift goal . args) . rest] (seq in out c ([goal . args] [== in out] . acc) temps heads . rest))
      ; the "trick": replace lifted goals by placeholders [[data]], and match on placeholders at the very end
      ; this sacrifices completeness by the ability to do sideways computation
      ([_ in out c acc temps [(ref: . heads) ac] (lift goal . args) rest ...]
       (let ([temp #false][data #false]) ; just to generate new temporaries
	  (seq temp out c ((appendo data temp in) . acc)
	     (temp data . temps) [(ref: . heads) ac] rest ...
	        (unlift goal data '() . args))
       )
      )
      ;; prevent runaway left-recursion
      ([_ in out c acc temps [(reb: . heads) ac] (lift goal . args) . rest]
       (let ([temp #false]) ; just to generate a new temporary
      	     (seq temp out c (#u [== in temp] . acc)
      		(temp . temps) [(reb: . heads) ac] . rest)
       )
      )
      ;; a little indirect way of doing the below.
      ; ([_ in out c acc temps [(reu: . heads) ac] (lift goal . args) . rest]
      ;  (let ([temp #false][data #false]) ; just to generate new temporaries
      ; 	  (seq temp out c ([goal data '() . args] (appendo data temp in). acc)
      ; 	     (temp data . temps) [(reu: . heads) ac] . rest)
      ;  ))
      ;; just generate left-recursive invocation, leading to divergence
      ([_ in out c acc temps [(reu: . heads) ac] (lift goal . args) . rest]
       (let ([temp #false]) ; just to generate a new temporary
      	     (seq temp out c ([goal in temp . args] . acc)
      		(temp . temps) [(reu: . heads) ac] . rest)
       )
      )
      ; the "trick": replace goals by placeholders and stitch it back in
      ([_ in out c acc temps heads (lift goal . args) rest ...]
       (let ([temp #false][data #false]) ; just to generate new temporaries
	  (seq temp out c ((appendo data temp in)
			    (project (in)
                            (if [ground? in]
				#s
			       (goal data '() . args)))
			 . acc)
	     (temp data . temps) heads rest ...
	        (unlift project (in)
		   (if [ground? in]
		       (goal data '() . args)
		       #s
	)))
       )
      )
      ; auto-lift the [[goal]] if found in [[heads]]
      ; (TODO maybe move others as well for optimization)
      ([_ in out c () temps [(r . heads) acc] (goal . args) . rest]
       (member?? goal heads
	  (seq in out c () temps [(r . heads) acc] (lift goal . args) . rest)
	  (let ([temp #false]) ; just to generate a new temporary
	     (seq temp out c ([goal in temp . args])
		(temp . temps) [(r . heads) acc] . rest)
	     )
       ))      
      ; regular goal
      ([_ in out c acc temps heads (goal . args) . rest]
	  (let ([temp #false]) ; just to generate a new temporary
	     (seq temp out c ([goal in temp . args]
			      . acc)
		(temp . temps) heads . rest)
	     )
      )
      ;; predicates
      ([_ in out c acc temps [heads (ac ...)] when guards . rest]
        ; temporary remains local
       (seq in out c ((let ([temp #false]) ; just to generate a new temporary
		      (fresh (temp)
			  (c ((seq in temp c () () [heads (ac ... . acc)] . guards) #s)
			     (else #u))
		       ))
		    . acc)
	  temps [heads (ac ...)] . rest))
      ([_ in out c acc temps [heads (ac ...)] unless guards . rest]
        ; temporary remains local
       (seq in out c ((let ([temp #false]) ; just to generate a new temporary
		      (fresh (temp)
			  (c ((seq in temp c () () [heads (ac ... . acc)] . guards) #u)
			     (else #s))
		      ))
		    . acc)
	  temps [heads (ac ...)] . rest))
      ; XXX this rule has to be last in this group
      ; auto-quote other terminals
      ([_ in out c acc temps heads datum . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([== in `(datum . ,temp)]
			 . acc)
	     (temp . temps) heads . rest)
       ))
      ))

(defn *def-extend* (λ (head) (λ (in out . results)
   #u
)))

(defn extend [make-parameter *def-extend*])

(def-syntax select (syntax-rules ()
 ([_ k () . _] k)
 ([_ (k ...) (1 . rest) a . l] (select (k ... a) rest . l))
 ([_ k (0 . rest) a . l] (select k rest . l))
))

(def-syntax [p-trf tag default k] (letrec-syntax ([p1 (syntax-rules ()
     ([_ dat ()]                 (revs (revs k (default tag)) dat))
     ([_ dat acc]                (revs (revs k acc) dat))
     ; will be reversed, so [[tag val]] -> [[val tag]]
     ([_ dat acc tag val . rest]  (p1 dat (val tag . acc) . rest))
     ([_ dat acc x . rest]        (p1 (x . dat) acc . rest))
    )])
    p1))

(def-syntax [comb tags kk . data]
 (letrec-syntax ([r (syntax-rules .. ()
   ([_ ()          k  _ . acc] (begin . acc))
   ([_ (a = (t v))       k pn . acc] (r [] k pn (let-syntax ([pn (p-trf t v kk)]) . acc)))
   ([_ (t v)       k pn . acc] (r [] k pn (let-syntax ([pn (p-trf t v kk)]) . acc)))
   ([_ (ts .. t v) k pn . acc]
    (r (ts ..) (pn [] []) pn (let-syntax ([pn (p-trf t v k)]) . acc)))
   )])
   (r tags (pn [] []) pn (pn [] [] . data))
))

(def-syntax make-scopes (syntax-rules (project)
       ([_ _ _ _] #s) ; is this really needed here? YES, for safety
       ([_ _ () head . body] (head . body))
       ([_ project (var ...) _ . body]
	(project (var ...)
	   (or (and (ground? var) ... . body) #s)
	))
       ([_ binder vars _ . body] 
	(let-syntax-rule ([K args terms]
	  (binder args . terms))
	  (extract* vars body (K [] body))
	  ))
       ))

(def-syntax process-args
  (letrec-syntax ([a (syntax-rules (proj π)
     ([a k acc [] goals rest (e es ...) aa res ps (locals ...)]
      (let-syntax-rule ([K . vars] ; collect the free vars 
      (let-syntax-rule ([K wv wp wt ws] ; use extracted vars
      (let-syntax ([K (syntax-rules ()
	; with no actions
	([_ pvars (ee . bis) pats ([] []) ()] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    ))
	([_ pvars (ee . bis) pats (terms []) ()] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    terms
	    ))
	([_ pvars (ee . bis) pats ([] []) hots] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    (make-scopes project pvars all . hots)
	    ))
	([_ pvars (ee . bis) pats (terms []) hots] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    terms
	    (make-scopes project pvars all . hots)
	    ))
	; with actions
	([_ pvars (ee . bis) pats ([] [Lin acts]) ()] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    (project (Lin) (if [ground? Lin] #s (begin . acts)))
	    (project (Lin) (if [ground? Lin] (begin . acts) #s))
	    ))
	([_ pvars (ee . bis) pats (terms [Lin acts]) ()] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    (project (Lin) (if [ground? Lin] #s (begin . acts)))
	    terms
	    (project (Lin) (if [ground? Lin] (begin . acts) #s))
	    ))
	([_ pvars (ee . bis) pats ([] [Lin acts]) hots] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    (project (Lin) (if [ground? Lin] #s (begin . acts)))
	    (project (Lin) (if [ground? Lin] (begin . acts) #s))
	    (make-scopes project pvars all . hots)
	    ))
	([_ pvars (ee . bis) pats (terms [Lin acts]) hots] ; use extracted vars
         (make-scopes fresh bis all
	    (let-syntax ([ee `()]) (all . pats))
	    (project (Lin) (if [ground? Lin] #s (begin . acts)))
	    terms
	    (project (Lin) (if [ground? Lin] (begin . acts) #s))
	    (make-scopes project pvars all . hots)
	    ))
	)])
	 (extract* vars (wp wt) (K () wv wp wt ws))
	 ))
	 (extract* (e es ... locals ... . vars) (res goals) (K () res goals ps))
	 ))
	 (scheme-bindings (w [] (K) (locals ...) aa))
	 ))
      ([a k acc [π arg . args] . rest]
       (a k acc [(proj arg) . args] . rest))
      ; first case, needed because we don't want a fresh [[result]]
      ([a k acc [(proj arg) . args] goals rest () aa (res ...) (ps ...) locals]
       (let ([e #false][t #false]) ;(fresh (e t)
       (a k acc args goals rest (e t) (arg . aa)
	  (res ... [== rest `(,t . ,e)])
	  (ps  ... [== t arg])
	  locals)
       ));)
      ; match the [[arg]] into the [[ee]]      
      ([a k acc [(proj arg) . args] goals rest (ee . es) aa (res ...) (ps ...) locals]
       (let ([e #false][t #false]) ;(fresh (e t)
       (a k acc args goals rest (e t ee . es) (arg . aa)
	  (res ... [== ee `(,t . ,e)])
	  (ps  ... [== t arg])
	  locals)
       ));)
      ; first case, needed because we don't want a fresh [[result]]
      ([a k acc [arg . args] goals rest () aa (res ...) ps locals]
       (let ([e #false]) ;(fresh (e)
       (a k acc args goals rest (e) (arg . aa)
	  (res ... [== rest `(,arg . ,e)])
	  ps
	  locals)
       ));)
      ; match the [[arg]] into the [[ee]]      
      ([a k acc [arg . args] goals rest (ee . es) aa (res ...) ps locals]
       (let ([e #false]) ;(fresh (e)
       (a k acc args goals rest (e ee . es) (arg . aa)
	  (res ... [== ee `(,arg . ,e)])
	  ps
	  locals)
       ));)
      ; start it (list of result elements is empty, list of destructuring actions empty,
      ; list of higher-order terms empty)
      ([a k acc args goals rest locals]
       (a k acc args goals rest () () () () locals)
       )
      )])
     a))
(def-syntax disj (syntax-rules (/)
 ([_ c (acc ...)]          (acc ... #u))
 ([_ c (acc ...) a]        (acc ... [(conj c [all] a)]))
 ([_ c (acc ...) a / . as] (disj c (acc ... [(conj c [all] a)]) . as))
))
;; TODO the same for (:)
(def-syntax conj (syntax-rules (/ : -> *->)
 ([_ c acc] acc)
 ([_ c (acc ...) (: . as) . rest]   (conj c (acc ... (conj c [all] . as)) . rest))
 ; XXX essential: [[then]] before [[if]] for reversibility
 ([_ c (acc ...) (if -> then) . rest] (conj c (acc ...
				(condu ([all (conj c [all] then) (conj c [all] if)]))) . rest))
 ; XXX essential: [[then]] before [[if]] for reversibility
 ([_ c (acc ...) (if -> then / else) . rest] (conj c (acc ...
				(condu ([all (conj c [all] then) (conj c [all] if)])
				       ((conj c [all] else))
				   )) . rest))
 ; XXX essential: [[then]] before [[if]] for reversibility
 ([_ c (acc ...) (if *-> then) . rest] (conj c (acc ...
				(conda ([all (conj c [all] then) (conj c [all] if)]))) . rest))
 ; XXX essential: [[then]] before [[if]] for reversibility
 ([_ c (acc ...) (if *-> then / else) . rest] (conj c (acc ...
				(conda ([all (conj c [all] then) (conj c [all] if)])
				       ((conj c [all] else))
				   )) . rest))
 ([_ c (acc ...) (a / . as) . rest]     (conj c (acc ... (disj c (c) a / . as)) . rest))
 ; conjunctions, keep track of : at the end
 ([_ c (acc ...) (a : as ... :) . rest] (conj c (acc ... a) (as ... :) . rest))
 ([_ c (acc ...) (a :) . rest]          (conj c (acc ... a) . rest))
 ([_ c (acc ...) (a : as ...) . rest]   (conj c (acc ... a) (as ... :) . rest))
 ; other predicate goals
 ([_ c (acc ...) pred . rest]           (conj c (acc ... pred) . rest))
))
;; TODO XXX introduce tracing via (#u)
;; TODO allow explicit naming of clauses via the first term
(def-syntax predicate
(letrec-syntax
([pred (syntax-rules .. (define begin _ fix <= <=> => :-)
 ([_ (k (define clh clb) ..) (fix head heads conde locals extend #f . foo)]
  (k (define clh clb) .. (define [head . args]
       (with-trace 4 'head (trace-item "args=" args)
	(let-syntax ([K (syntax-rules ()
	; TODO XXX remove conde if only one clause (according to Oleg its needed)
	([_ #f] (conde (#u) ((apply clh args)) ..))
	([_ ex] (conde ((apply [(ex) 'head] args))
	               ((apply clh args)) ..))
	)])
	   (K extend)
	)))
  ))
 ([_ (k (define clh clb) ..) (any head heads conde locals extend #f . foo)]
  (let ()
     (k (define clh clb) .. (define [head . args]	
       (with-trace 4 'head (trace-item "args=" args)
        ;XXX no extensibility here since [[any head]] is a eigen-variable and
	;we don't know how this [[conde]] should be extended (no [[phead]])
	; TODO XXX remove conde if only one clause (according to Oleg its needed)
	(conde (#u) ((apply clh args)) ..
	))))
     head))
 ; extensible version of the encapsulated goal, if the [[phead]] is given
 ; needed for predicates
 ([_ (k (define clh clb) ..) (any head heads conde locals extend phead . foo)]
  (let ()
     (k (define clh clb) .. (define [head . args]
       (with-trace 4 'phead (trace-item "args=" args)
	(let-syntax ([K (syntax-rules ()
	; TODO XXX remove conde if only one clause (according to Oleg its needed)
	([_ #f] (conde (#u) ((apply clh args)) ..))
	([_ ex] (conde ((apply [(ex) 'phead] args))
	               ((apply clh args)) ..))
	)])
	   (K extend)
	))))
     head))
 ; Horn clauses
 ([_ (begin ks ..) params ([_ . args]) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K conde locals phead]
  (pred (begin ks ..
    (define head (λ vars
      (with-trace 4 'head (trace-item "vars=" vars)
      ;[[locals]] merged with other vars in [[process-args]] now
      ;(make-scopes fresh locals begin
       (process-args conde (ks ..) args ([] []) vars locals)
       )))
    ) params . rest))
  (select (K) (0 0 0 1 1 0 1) . params)
  )))
 ([_ (begin ks ..) params ([_ . args] :- . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K conde locals phead]
  (pred (begin ks ..
    (define head (λ vars
      (with-trace 4 'head (trace-item "vars=" vars)
      ;[[locals]] merged with other vars in [[process-args]] now
      ;(make-scopes fresh locals begin
       (process-args conde (ks ..) args ([conj conde [all] . body]
					 ;[all . body]
					 [])
	  vars
	  locals)		    
       )))
    ) params . rest))
  (select (K) (0 0 0 1 1 0 1) . params)
  )))
 ;; DCG rules
 ([_ (begin ks ..) params ([] <=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals begin
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([_] <=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals all
       [appendo vars Lout Lin]
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([|.|] <=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh (results . locals) all
	 [appendo results Lout Lin]
	 [== vars `(,results)]
	 [seq Lin Lout conde () () [heads (ks ..)] . body]
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([_ . args] <=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals phead]
   (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      ;(pp 'heads)
      ;[[locals]] merged with other vars in [[process-args]] now
      ;(make-scopes fresh locals begin
       (process-args conde (ks ..) args
	  ([seq Lin Lout conde () () [heads (ks ..)] . body] [])
	  vars
	  locals)
       )))
    ) params . rest))
     (select (K) (0 0 1 1 1 0 1) . params)
  )))
 ([_ (begin ks ..) params ([an arg ..] <=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals all
       [== vars `(,arg ..)]
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ;; effectful PCG rules
 ([_ (begin ks ..) params ([] <=[actions ..]=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals all
       (project (Lin) (if [ground? Lin] #s (begin actions ..)))
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       (project (Lin) (if [ground? Lin] (begin actions ..) #s))
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([_] <=[actions ..]=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals all
       [appendo vars Lout Lin]
       (project (Lin) (if [ground? Lin] #s (begin actions ..)))
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       (project (Lin) (if [ground? Lin] (begin actions ..) #s))
      ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([|.|] <=[actions ..]=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh (results . locals) all
	 [appendo results Lout Lin]
	 [== vars `(,results)]
	 (project (Lin) (if [ground? Lin] #s (begin actions ..)))
	 [seq Lin Lout conde () () [heads (ks ..)] . body]
	 (project (Lin) (if [ground? Lin] (begin actions ..) #s))
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
   )))
 ([_ (begin ks ..) params ([_ . args] <=[actions ..]=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      ;[[locals]] merged with other vars in [[process-args]] now
      ;(make-scopes fresh locals begin
       (process-args conde (ks ..) args
	  ([seq Lin Lout conde () () [heads (ks ..)] . body] [Lin (actions ..)])
	  vars
	  locals)
       )))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 ([_ (begin ks ..) params ([an arg ..] <=[actions ..]=> . body) . rest]
  (let-syntax ([head #false])
  (let-syntax-rule ([K heads conde locals]
  (pred (begin ks ..
    (define head (λ (Lin Lout . vars)
      (with-trace 4 'head (trace-item (trace-bold "Lin=" Lin) ",vars=" vars (trace-bold ",Lout=" Lout))
      (make-scopes fresh locals all
       [== vars `(,arg ..)]
       (project (Lin) (if [ground? Lin] #s (begin actions ..)))
       [seq Lin Lout conde () () [heads (ks ..)] . body]
       (project (Lin) (if [ground? Lin] (begin actions ..) #s))
       ))))
    ) params . rest))
     (select (K) (0 0 1 1 1) . params)
  )))
 )])
 (syntax-rules (=)
 ; simple renaming, two cases needed because of [[predicates]] below
  ([_ heads: heads condo: condo locals: locals extend: extend head: #f trace: t memo: m
    head = tail] (define head tail))
  ([_ heads: heads condo: condo locals: locals extend: extend head: h trace: t memo: m
    = tail] tail)
 ; for the next 2 rules, locals are not extracted here, but by [[make-scopes]]
 ; the [[head]] is our eigen-variable
  ([_ heads: heads condo: condo locals: locals extend: extend head: h trace: t memo: m
    (clh . clb) ...]
     (pred [begin] (any head heads condo locals extend h t m) (clh . clb) ...))
 ; the [[head]] is given by the user
  ([_ heads: heads condo: condo locals: locals extend: extend head: h trace: t memo: m
    head (clh . clb) ...]
     (pred [begin] (fix head heads condo locals extend h t m) (clh . clb) ...))
  
 ; record the head as the potentially recursive predicate
  ([_ head . rest]
   (symbol?? head
    (comb (heads: (rev: head) condo: conde locals: () extend: #f head: #f trace: #f memo: #f)
      (predicate) head . rest)
    (comb (heads: (rev:) condo: conde locals: () extend: #f head: #f trace: #f memo: #f)
      (predicate) head . rest)
   ;(predicate heads:() . rest)
   ))
)))

(def-syntax predicates
 (let-syntax ([gen (syntax-rules ()
 ; flat transparent case
 ([_ tag (nam . def) ...]
  (let-syntax ([K (syntax-rules .. ()
  ([_ (name ..) hds (defs ..)]
    (begin (predicate heads: (tag . hds) name . defs) ..))
   )])
   (extract* (nam ...) (nam ... def ...) (K [] (nam ...) [def ...]))
   ))
 ; encapsulate via a start symbol
 ([_ tag start (nam . def) ...]
  (let-syntax ([K (syntax-rules .. ()
  ([_ (strt name ..) hds (defs ..)]
    (let ()
       (define name (predicate head: name heads: (tag . hds) . defs)) ..
       strt))
   )])
   (extract* (start nam ...) (nam ... def ...) (K [] (nam ...) [def ...]))
   ))
  )])
 (syntax-rules (<= <=> => <=:)
 ; pass the anonymous predicate handling down
 ([_ ([head ...] . def) ...] (predicate ([head ...] . def) ...))
 ; flat transparent case
 ([_ (name . def) ...] (gen rev: (name . def) ...))
 ; encapsulated case
 ([_ <=> . rest] (gen rev: . rest))
 ([_ => . rest] (gen ref: . rest))
 ([_ <= . rest] (gen reb: . rest))
 ([_ <=: . rest] (gen reu: . rest))
 ; pass the named predicate handling down
 ([_ . rest] (predicate . rest))
)))

(def-syntax pcg predicates)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def appendo (predicate
 ([_ `() b b])
 ([_ `(,x . ,a1) b `(,x . ,c1)] :- [appendo a1 b c1])
))
