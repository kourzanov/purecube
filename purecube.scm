#! /usr/bin/env bgl
(cond-expand (bigloo-eval
(module parse
   (library srfi1 slib minikanren)
   (import brackets
	   (helpers "helpers.scm")
	   (ascript "cases.scm"))
   (eval (export-exports)))
)(else
(module parse
   (library srfi1 slib minikanren)
   (eval (export-exports)))
(load "synrules.sch")
(load "dodger.sch")
(load "cases.scm")
(load "cond-expand.sch")
(load "forall.scm")
(load "helpers.scm")
(load "brace-syntax.sch")
(load "bracket-syntax.sch")
))

(load "debug.scm")
(load "loprog.sch")

(def-syntax ∘ compose)
(def-syntax _ rcurry)
(def-syntax _.x lcurry)
(def-syntax :: cons)
;(def-syntax epsilon ε)
(def-syntax λ lambda)

(def *digits* (make-parameter
  (list-tabulate 10 values)))

(def *letters* (make-parameter
  (unfold [_ char>? #\z]
     values
     (∘ integer->char
	[_ $+ 1]
	char->integer)
     #\a)))

;(write *letters*)

(def (numbers? x)
   (take-from [*digits*] x)
   ; (project (x)
   ;   (cond ([number? x] #s)
   ; 	   (else #u)))
)

(def (symbols? x)
   (take-from (map (∘ string->symbol 
   		      list->string
   		      list)
   		 [*letters*]) x)
   ; (project (x)
   ;   (cond ([symbol? x] #s)
   ; 	   (else #u)))
)

(def (number Lin Lout x)
 (all
    (numbers? x)
    (consᵒ x Lout Lin)
 ))

(def (symbol Lin Lout x)
 (all
   (symbols? x)
   (consᵒ x Lout Lin)
 ))

(verify number (run* (q) (fresh (X) (number '(2 a 3) X q))) ===> 2)
(verify symbol (run* (q) (fresh (X) (symbol '(a 3) X q)))   ===> a)

; literal --> symbol.
; literal --> number.
(def (literal Lin Lout x)
   (conde ([symbol Lin Lout x])
          ([number Lin Lout x])))

(verify literal (run* (q) (fresh (X) (literal '(2 ^ 3) X q))) ===> 2) 
(verify literal (run* (q) (fresh (X) (literal q X 4)))        ===> (4 . _.0))

(def (skipn n a b)
   (if [> n 0]
       (fresh (_ c)
	  (== a `(,_ . ,c))
	  (skipn (-1+ n) c b))
       (== a b)))

(verify skipn (run* (q) (skipn 0 '(1 2) q)) ===> (1 2))
(verify skipn (run* (q) (skipn 1 '(1 2) q)) ===> (2))
(verify skipn (run* (q) (skipn 2 '(1 2) q)) ===> ())
(verify skipn (run* (q) (skipn 3 '(1 2) q)) =>) ; should fail

;(revs (list) (1 2 3))
; (define-syntax rev (syntax-rules ()
;    ([_ () () r] r)
;    ([_ k (h . t) r] (rev k t (h . r)))
; ))
;(rev () (1 2 3) ())

; Because we are replacing all potential immediate mutual infinite recursive rules by FAIL (#u)
; in cases when they are the only sub-goals in the first rule of a goal, such situations can be
; circumvented by reordering the rules see Hutton's Razor with exponents below
;
; TODO: alexpander can handle (fresh (bindings ...)) natively
; (really needed? compiler can remove by constant β-reduction)
; so that we don't need to generate new temporaries via (let ((bindings #false)...))
; TODO: rename to PCG?
(def-syntax dcg
 (letrec-syntax 
  ([revs (syntax-rules ()
       ([_ () () . r] r)
       ([_ (k args ...) () . r] (k args ... . r))
       ([_ k (h . t) . r] (revs k t h . r))
       )]
   [revv (syntax-rules ()
       ([_ () r] r)
       ([_ (k args ...) r] (k args ... . r))
       ([_ k r h . t] (revv k t h . r))
       )]
  [hd (syntax-rules () ([_ a . _] a))]
  [zip2 (syntax-rules … ()
	([_ (k …) () () . a] (k … . a))
	([_ k (x . xs) (y . ys) . a] (zip2 k xs ys (x y) . a))
	 )]
  [zip3 (syntax-rules … ()
	([_ (k …) () () () . a] (k … . a))
	([_ k (x . xs) (y . ys) (z . zs) . a] (zip3 k xs ys zs (x y z) . a))
	 )]
  [zip4 (syntax-rules … ()
	([_ (k …) () () () () . a] (k … . a))
	([_ k (x . xs) (y . ys) (z . zs) (w . ws) . a] (zip4 k xs ys zs ws (x y z w) . a))
	 )]
  [make-fresh (syntax-rules ()
       ([_ () head . body] (head . body))
       ([_ vars _ . body] (fresh vars . body))
       )]
  [member?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (id . ids) xs kt kf] kf)
      ([_ id (x . r) kt kf]
       (let-syntax ([test (syntax-rules (id)
			     ([_ id t f] t)
			     ([_ xx t f] f))])
	  (test x kt (member?? id r kt kf))
	  )))]
  [proc-/ (syntax-rules (/)
	([_ in out c (k ...) heads] (k ... #u))
	([_ in out c (k ...) heads a] (k ... ((seq in out c () () heads a))))
	([_ in out c (k ...) heads a / . as] (proc-/ in out c (k ... ((seq in out c () () heads a))) heads . as))
	)]
  [qs (syntax-rules .. (qq quote unquote quasiquote unquote-splicing) 
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
     )]
  [scheme-bindings (syntax-rules .. ()
    ([_ (k a b [s ..] . d)] (k a b [s .. list first second pair? car cdr null? if cond begin + - * /] . d))
    )]
  [w (syntax-rules .. (qq quote unquote quasiquote unquote-splicing
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
     )]
  [seq
   (syntax-rules (qq quote unquote quasiquote unquote-splicing
		  do ε when unless skip ? + * / : lift unlift)
      ; rev: ref: reb:)
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
      ([_ in out _ acc temps heads do(actions ...)]     (revs (make-fresh temps begin) (actions ... . acc)))
      ; delegate this both to ^^^
      ([_ in out c acc temps heads ε]             (seq in out c acc temps heads do[(== in out)]))
      ; XXX TODO remove this? (its not reversible)
      ; since this is the last rule, no further [[clashes]] for temp can ensue
      ; and we don't need to generate a new temporary
      ([_ in out c acc temps heads (skip n)]      (seq in out c acc temps heads do[(skipn n in out)]))
      ([_ in out c acc temps heads skip]          (seq in out c acc temps heads do[(fresh (_) (== in `(,_ . ,out)))]))
      ; terminals
      ([_ in out c acc temps heads (quote datum)] (seq in out c acc temps heads do[(== in `(datum . ,out))]))
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
      ([_ in out c acc temps heads (alt / . alts)]
        (seq in out c acc temps heads do[(proc-/ in out c (c) heads alt / . alts)]
       ))
      ;; [[*]] combinator that collects functor arguments for all [[goals]] into
      ;; lists as it iterates on the input
      ([_ in out c acc temps [(r . heads) (ac ...)] (goals ... *)]
      (let-syntax ([K (syntax-rules .. ()
       ; we need to explicitly get the [[in]] and [[out]] from the caller
       ([_ in out vars ..] ; 1st bunch
	(let loop ([lin in][lout out] [vars '()] ..)
	(let-syntax ([K (syntax-rules … ()
	([_ res …] ; 2nd bunch
	  (let ([res #false] …)
	  (make-fresh (res …) begin
	   (letrec-syntax ([K (syntax-rules .... ()
	   ([_ gls (v v1 v2 v3) ....]
	    ; and now declare the 3rd bunch of vars
	    ; and substitute it for the original var in [[gls]]==[[goals]]
	    (c ([== lin lout]
		(== v1 v) ....)
	       ((let ([temp #false][v3 #false] ....)
		(fresh (temp v3 ....)
		   ; rename original var to a local temporary
		   (let-syntax ([v v3] ....)
		      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
		      )
		   (appendo v1 `(,v3) v2) ....
		   [loop temp lout v2 ....])
		)
		))
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
      ;; XXX simplified [[*]] combinator where we don't want to get the matched lists
      ([_ in out c acc temps [heads (ac ...)] (goals ... *)]
       (seq in out c acc temps [heads (ac ...)] 
	  do[(let loop ([lin in][lout out])
		(c ([== lin lout])
		   ((let ([temp #false]) ; just to generate a new temporary
		    (fresh (temp)
			  (seq lin temp c () () [heads (ac ... . acc)] goals ...)
			  (loop temp lout)
		     ))
		    )
		   ))]
       ))
      ;; [[+]] combinator that collects functor arguments for all [[goals]] into
      ;; lists as it iterates on the input
      ([_ in out c acc temps [(r . heads) (ac ...)] (goals ... +)]
      (let-syntax ([K (syntax-rules .. ()
       ; we need to explicitly get the [[in]] and [[out]] from the caller
       ([_ in out vars ..] ; 1st bunch
	(let loop ([lin in][lout out] [vars '()] ..)
	(let-syntax ([K (syntax-rules … ()
	([_ res …] ; 2nd bunch
	  (let ([res #false] …)
	  (make-fresh (res …) begin
	   (letrec-syntax ([K (syntax-rules .... ()
	   ([_ gls (v v1 v2 v3) ....]
	    ; and now declare the 3rd bunch of vars
	    ; and substitute it for the original var in [[gls]]==[[goals]]
	    (let ([temp #false][v3 #false] ....)
	    (fresh (temp v3 ....)
	      ; rename original var to a local temporary
	      (let-syntax ([v v3] ....)
	      (seq lin temp c () () [(r . heads) (ac ... . acc)] . gls)
	      )
	      (c ([== temp lout]
		  (appendo v1 `(,v3) v) ....)
		 ((appendo v1 `(,v3) v2) ....
		  [loop temp lout v2 ....])
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
      ;; XXX simplified [[+]] combinator where we don't want to get the matched lists
      ([_ in out c acc temps [heads (ac ...)] (goals ... +)]
       (seq in out c acc temps [heads (ac ...)] 
	  do[(let loop ([lin in][lout out])
		(let ([temp #false]) ; just to generate a new temporary
		(fresh (temp)
		       (seq lin temp c () () [heads (ac ... . acc)] goals ...)
		       (c ([== temp lout])
			  ([loop temp lout]))
		))
	   )]
       ))
      ;<=: support, we know left-recursion won't hurt
      ([_ in out c () temps [(reu: . heads) ()] (lift goal . args)] (seq in out c () temps [(reu: . heads) ()] do[(goal in out . args)]))
      ;don't need to muck around with the tail-recursive call (if it is the only one, no way to avoid bottom)
      ([_ in out c () temps [(x . heads) ()] (lift goal . args)] (seq in out c () temps [(x . heads) ()] do[#u (== in out)]))
      ([_ in out c acc temps heads (lift goal . args)] (seq in out c acc temps heads do[(goal in out . args)]))
      ;tie the knot, and then do the call recursively
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
      ;; TODO: delegate processing for all sub-patterns, just like for [[+]] and [[*]]
      ; collect all actions and rules in the [[acc]]
      ([_ in out c acc temps heads do(actions ...) . rest] (seq in out c (actions ... . acc) temps heads . rest))
      ([_ in out c acc temps heads ε . rest]         (seq in out c ([== in out] . acc) temps heads . rest))
      ; TODO remove this? (its not reversible)
      ([_ in out c acc temps heads (skip n) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([skipn n in temp]
			 . acc)
	     (temp . temps) heads . rest)
       )
       )
      ([_ in out c acc temps heads skip . rest]
       (let ([temp #false][_ #false]) ; just to generate new temporaries
	  ; temp is propagated, along with _ for efficiency
	  (seq temp out c ([== in `(,_ . ,temp)]
			 . acc)
	     (temp _ . temps) heads . rest)
       )
       )
      ; terminals
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
      ([_ in out c acc temps heads (alt / . alts) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ([proc-/ in temp c (c) heads alt / . alts]
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
      ;; XXX old, simplified [[*]] combinator
      ([_ in out c acc temps [heads (ac ...)] (goals ... *) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ((let loop ([lin in][lout temp])
				 (c ([== lin lout])
				    ((let ([temp #false]) ; just to generate a new temporary
				     (fresh (temp)
					   (seq lin temp c () () [heads (ac ... . acc)] goals ...)
					   (loop temp lout)
				      ))
				     )
				    ))
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
      ;; XXX old, simplified [[+]] combinator
      ([_ in out c acc temps [heads (ac ...)] (goals ... +) . rest]
       (let ([temp #false]) ; just to generate a new temporary
	  (seq temp out c ((let loop ([lin in][lout temp])
			      (let ([temp #false]) ; just to generate a new temporary
			      (fresh (temp)
				     (seq lin temp c () () [heads (ac ... . acc)] goals ...)
				     (c ([== temp lout])
					([loop temp lout]))
			       )))
			   . acc)
	     (temp . temps) [heads (ac ...)] . rest)
       )
      )
      ; automatically lift left-recursive calls, if it is the first one
      ; (TODO maybe move others as well for optimization)
      ;([_ in out c () temps heads (head . args) . rest]
      ; (seq in out c () temps (lift head . args) . rest))
      ; handle only left-recursive rules
      ;([_ in out c acc temps (head . args) . rest]
      ; (seq in out c acc temps (lift head . args) . rest))
      
      ; accumulate recursive calls in the tail (tie the knot in the last recursive call, see above)
      ([_ in out c acc temps heads (unlift goal . args) . rest] (seq in out c ([goal . args] . acc) temps heads . rest))
      ; the "trick": replace lifted goals by placeholders [[data]], and match on placeholders at the very end
      ; this sacrifices completeness by the ability to do sideways computation
      ([_ in out c acc temps [(ref: . heads) ac] (lift goal . args) rest ...]
       (let ([temp #false][data #false]) ; just to generate new temporaries
	  (seq temp out c ((appendo data temp in) . acc)
	     (temp data . temps) [(ref: . heads) ac] rest ...
	        (unlift goal data '() . args))
       )
      )
      ;; a little indirect way of doing the below.
      ; ([_ in out c acc temps [(reb: . heads) ac] (lift goal . args) . rest]
      ;  (let ([temp #false][data #false]) ; just to generate new temporaries
      ; 	  (seq temp out c ([goal data '() . args] (appendo data temp in). acc)
      ; 	     (temp data . temps) [(reb: . heads) ac] . rest)
      ;  ))
      ;; prevent runaway left-recursion
      ([_ in out c acc temps [(reb: . heads) ac] (lift goal . args) . rest]
       (let ([temp #false]) ; just to generate a new temporary
      	     (seq temp out c (#u [== in temp] . acc)
      		(temp . temps) [(reb: . heads) ac] . rest)
       )
      )
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
      )]
  )
 (syntax-rules .. (locals: condo: heads: <= => <=> <=:)
 ;; mutually recursive rules
 ;; hiding/encapsulating sub-goals
 ; reversible, complete, works forwards and backwards with run*, also for left-recursive rules
 ([_ <=> start (head . args) ..] (dcg start () (rev: head ..) => (head . args) ..))
 ; sideways, incomplete, works forwards, backwards with run(N), and sideways, also to left-recursive rules
 ([_ => start (head . args) ..] (dcg start () (ref: head ..) => (head . args) ..))
 ; just disable "the trick", only works backwards for right-recursive rules, left-recursive rules are prevented via FAIL (#u)
 ([_ <= start (head . args) ..] (dcg start () (reb: head ..) => (head . args) ..))
 ; just disable "the trick", only works backwards for right-recursive rules
 ([_ <=: start (head . args) ..] (dcg start () (reu: head ..) => (head . args) ..))
 ([_ st (acc ..) ach =>] (let () ;(pp 'ach)
			acc ..
			st))
 ([_ st acc ach => [head . args] . rest]
  (dcg st ((dcg head heads: ach . args) . acc)
       ach
       => . rest))
 ; many possibly mutually recursive clauses,
 ; each is visible from the outside
 ([_ (head . args) ..]
  (let-syntax-rule ([k . heads]
     (begin ;(pp 'heads)
	(dcg head heads: (rev: . heads) . args) ..
	))
     (k head ..)
    ))
 ; one clause
 ([_ head heads: heads locals: locals condo: condo . rules]
  ;(begin ;(pp 'heads)
  [define head (λ (Lin Lout . result)
  (letrec-syntax
   ; DONE add special syntax for the head to auto-propagate matched input to the output
   ; DONE auto-extract locals: infer them from the head vars
   ([p (syntax-rules ... (<=> <= => _ proj)
	 ([p k acc] (revs (k) acc))
	 ; assume the user wants to get matched lists as a single packaged result
	 ([p k acc ([] <=> . goals) . rest]
	  (p k ([(fresh (results)
		    (appendo results Lout Lin)
		    (== result `(,results))
		    (seq Lin Lout k () () [heads acc] . goals))] . acc) . rest)
	 )
	 ; assume the user gives the uncurried arguments 
	 ([p k acc ([_] <=> . goals) . rest]
	  (p k ([(all (appendo result Lout Lin)
		      (seq Lin Lout k () () [heads acc] . goals))] . acc) . rest)
	 )
	 ; can be used to inject the result into a higher-order function.
	 ; the result has to be matched after the parse since we need to project it first
	 ([p k acc ([_ (proj args ...)] <=> . goals) . rest]
	  (let-syntax-rule ([K . vars] ; collect the free vars 
	  (let-syntax-rule ([K vars pats terms] ; use extracted vars
	    (make-fresh vars all
	       (seq Lin Lout k () () [heads acc] . terms)
	       (project vars [== result pats])
	       ))
	     ; extract coulored bindings for [[vars]] from [[args]] and [[goals]]
	     (extract* vars (args ... . goals) (K () `(,args ...) goals))
	     ))
	     ; extract free vars from [[args]] ...
	     (p k (([scheme-bindings (w [] (K) [] (args ...))]) . acc) . rest)
	     ))	 
	 ; DONE introduce fresh vars here
	 ([p k acc ([_ args ...] <=> . goals) . rest]
	  (let-syntax-rule ([K . vars] ; collect the free vars 
	  (let-syntax-rule ([K vars pats terms] ; use extracted vars
	    (make-fresh vars all
	       [== result pats]
	       (seq Lin Lout k () () [heads acc] . terms)
	       ))
	     ; extract coulored bindings for [[vars]] from [[args]] and [[goals]]
	     (extract* vars (args ... . goals) (K () `(,args ...) goals))
	     ))
	     ; extract free vars from [[args]] ...
	     (p k (([scheme-bindings (w [] (K) [] (args ...))]) . acc) . rest)
	     ))
	 ; the user remains in control of the bindings done in [[args]] and [[goals]]
	 ([p k acc ([x args ...] <=> . goals) . rest]
	  (p k ([(all [== result `(,args ...)]
		      (seq Lin Lout k () () [heads acc] . goals))] . acc) . rest)
	 )
	 ; assume the user wants to get matched lists as a single packaged result
	 ([p k acc ([] <=[actions ...]=> . goals) . rest]
	  (p k ([(fresh (results)
		      (appendo results Lout Lin)
		      (== result `(,results))
		      (project (Lin) (if [ground? Lin] #s (begin actions ...)))
		      (seq Lin Lout k () () [heads acc] . goals)
		      (project (Lin) (if [ground? Lin] (begin actions ...) #s))
		      )]
		. acc)
	     . rest))
	 ; assume the user gives the uncurried arguments 
	 ([p k acc ([_] <=[actions ...]=> . goals) . rest]
	  (p k ([(all (appendo result Lout Lin)
		      (project (Lin) (if [ground? Lin] #s (begin actions ...)))
		      (seq Lin Lout k () () [heads acc] . goals)
		      (project (Lin) (if [ground? Lin] (begin actions ...) #s))
		      )]
		. acc)
	     . rest))
	 ; can be used to inject the result into a higher-order function.
	 ; the result has to be matched after the parse since we need to project it first
	 ([p k acc ([_ (proj args ...)] <=[actions ...]=> . goals) . rest]
	  (let-syntax-rule ([K . vars] ; collect the free vars 
	  (let-syntax-rule ([K vars pats terms] ; use extracted vars
	    (make-fresh vars all
	       (project (Lin) (if [ground? Lin] #s (begin actions ...)))
	       (seq Lin Lout k () () [heads acc] . terms)
	       (project (Lin) (if [ground? Lin] (begin actions ...) #s))
	       (project vars [== result pats])
	       ))
	     ; extract coulored bindings for [[vars]] from [[args]] and [[goals]]
	     (extract* vars (args ... . goals) (K () `(,args ...) goals))
	     ))
	     ; extract free vars from [[args]] ...
	     (p k (([scheme-bindings (w [] (K) [] (args ...))]) . acc) . rest)
	     ))	 
	 ; DONE introduce fresh vars here
	 ([p k acc ([_ args ...] <=[actions ...]=> . goals) . rest]
	  (let-syntax-rule ([K . vars] ; collect the free vars 
	  (let-syntax-rule ([K vars pats terms] ; use extracted vars
	    (make-fresh vars all
	       [== result pats]
	       (project (Lin) (if [ground? Lin] #s (begin actions ...)))
	       (seq Lin Lout k () () [heads acc] . terms)
	       (project (Lin) (if [ground? Lin] (begin actions ...) #s))
	       ))
	     ; extract coulored bindings for [[vars]] from [[args]] and [[goals]]
	     (extract* vars (args ... . goals) (K () `(,args ...) goals))
	     ))
	     ; extract free vars from [[args]] ...
	     (p k (([scheme-bindings (w [] (K) [] (args ...))]) . acc) . rest)
	     ))
	 ; the user remains in control of the bindings done in [[args]] and [[goals]]
	 ([p k acc ([x args ...] <=[actions ...]=> . goals) . rest]
	  (p k ([(all [== result `(,args ...)]
		      (project (Lin) (if [ground? Lin] #s (begin actions ...)))
		      (seq Lin Lout k () () [heads acc] . goals)
		      (project (Lin) (if [ground? Lin] (begin actions ...) #s))
		      )]
		. acc)
	     . rest))

	 )])
   (condo [(apply extend 'head Lin Lout result)]
     (else
      (make-fresh locals begin
	(p condo [] . rules)
	))
     ))
  )])
 ; default arguments & ordering
 ([_ head heads: heads locals: locals condo: condo . rules] (dcg head heads: heads locals: locals condo: condo . rules))
 ([_ head heads: heads condo: condo locals: locals . rules] (dcg head heads: heads locals: locals condo: condo . rules))
 ([_ head heads: heads locals: locals . rules] (dcg head  heads: heads locals: locals condo: conde . rules))
 ([_ head heads: heads condo: condo . rules]   (dcg head  heads: heads locals: ()     condo: condo . rules))
 ([_ head heads: heads . rules]                (dcg head  heads: heads locals: ()     condo: conde . rules))
 
 ([_ head locals: locals condo: condo . rules] (dcg head heads: (rev: head) locals: locals condo: condo . rules))
 ([_ head condo: condo locals: locals . rules] (dcg head heads: (rev: head) locals: locals condo: condo . rules))
 ([_ head locals: locals . rules] (dcg head  heads: (rev: head) locals: locals condo: conde . rules))
 ([_ head condo: condo . rules]   (dcg head  heads: (rev: head) locals: ()     condo: condo . rules))
 ([_ head . rules]                (dcg head  heads: (rev: head) locals: ()     condo: conde . rules))
 )))

(def (extend head in out . results)
   #u
)

(def-syntax peg (syntax-rules (<= <=> => <=:)
  ([_ <=> start (head . args) ...]
   (dcg <=> start (head condo: condu . args) ...))
  ([_ => start (head . args) ...]
   (dcg => start (head condo: condu . args) ...))
  ([_ <= start (head . args) ...]
   (dcg <= start (head condo: condu . args) ...))
  ([_ <=: start (head . args) ...]
   (dcg <=: start (head condo: condu . args) ...))
  ([_ (head . args) ...]
   (dcg (head condo: condu . args) ...))
  ([_ head . args]
   (dcg head condo: condu . args))
))

; has to be PEG because of multi-result behavior
; Here we change left-recursion to right-recursion for the expression grammar
; associativity is a problem for ^ operator
; factor(pow(x,times(y . z))) --> literal(x), [^], factor(pow(y,times(.z).
(defn factor (peg <= factor
(factor ;locals: (x y z l)
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
(verify factor (run 0 (q) (fresh (x y z) (factor x  y z) (== q `(,x ,y ,z)))) --->)

;(exit)
(def (appendo a b c)
   (conde
    ([== a '()] (== b c))
    ;([== b '()] (== a c))
    (else (fresh (x a1 c1)
	   (== a `(,x . ,a1))
	   (== c `(,x . ,c1))
	   (appendo a1 b c1)))
    ))

(verify appendo (run* (q) (appendo q '(3) '(1 2 3))) ===> (1 2))
(verify appendo (run* (q) (appendo '(1 2) q '(1 2 3))) ===> (3))
(verify appendo (length (run* (q) (fresh (x y) (appendo x y '(1 2 3)) (== q `(result: ,x ,y))))) = 4)
(verify appendo (run* (q) (fresh (x y) (appendo '(1 2) x y) (== q `(result: ,x ,y)))) ===> (result: _.0 (1 2 . _.0)))
; appendo can handle non-ground [[x]] and [[y]]!
(verify appendo (run 2 (q) (fresh (x y) (appendo x '(3) y) (== q `(,x ,y)))) ---> (() (3)) ((_.0) (_.0 3)))

(def (reve a b c)
 (fresh (x xs)
   (condu ((all [== a '()] [== b c]))
          ; ((all [== b '()] [== a c]))
          ; ((all [== b `(,x . ,xs)] 
	  ;       [reve a xs `(,x . ,c)]))
          ((all [== a `(,x . ,xs)] 
	        [reve xs b `(,x . ,c)]))
	  )))

(verify reve (run* (q) (reve '(1 2 3) q '())) ===> (3 2 1))
(verify reve (run* (q) (reve q '(1 2 3) '())) ===> (3 2 1))
(verify reve (run* (q) (reve '(1 2 3) q '(0))) ===> (3 2 1 0))
;(verify reve (run* (q) (reve q '(1 2 3) '(4))) ===> (3 2 1 4))



;old stuff
(dcg term' ;locals: (x y)  
 ([_ `(* ,x . ,y)] <=> (factor x) '* (term' `(* . ,y))) ; optimize associative Scheme's * - no fixing needed
 ([_ `(* ,x ,y)] <=> (factor x) '* (term' y))           ; do[trace-vars 'term (x y)])
 ([_ `(/ ,x . ,y)] <=> (factor x) '/ (term' `(/ . ,y))) ; rely on correct variadic /
 ([_ `(/ ,x ,y)] <=> (factor x) '/ (term' y))
 ([_ x] <=> (factor x))
 )

; should have quadratic complexity
(def (pushdown x o a b)
  (fresh (y z l)   
   (condu ([all (== b `(,o ,l ,z))
                (== a `(,o ,y ,z))
                (pushdown x o y l)])
          ([== b `(,o ,x ,a)])
)))

(def (sameops ops y)
 (fresh (x z o)
   (take-from ops o)
   (== y `(,o ,x . ,z))))

; <= prefents runaway left-recursion, [[defn]] prevents self-recursion circumventing <= mechanism
(defn term (dcg <= term
(term locals: (x y z l o)
 ; test left-recursion prevention (by <= and defn)
 ([term `(* ,l . ,z)] <=> (term `(* ,y . ,z)) '* (factor x))
 ;
 ([term `(* ,l . ,z)] <=[(pushdown x '* y l)]=> (factor x) '* (term `(* ,y . ,z)))
 ([term `(* ,x ,y)]   <=[(! sameops '(*) y)]=> (factor x) '* (term y))
 ([term `(/ ,l . ,z)] <=[(pushdown x '/ y l)]=> (factor x) '/ (term `(/ ,y . ,z)))
 ([term `(/ ,x ,y)]   <=[(! sameops '(/) y)]=> (factor x) '/ (term y))
 ;([_ `(,o ,l . ,z)] <=[(push-down x o y l)]=> (factor x) (term-op o) (term `(,o ,y . ,z)))
 ; ;([_ `(,o ,x ,y)] <=[(! sameops '(* /) y)]=> (factor x) (term-op o) (term y))
 ;([_ `(,o ,x ,y)] <=> (factor x) (term-op o) (term y))
 ([term x] <=> (factor x))
 )))

(verify term (run* (q) (fresh (x) (term '(1 * 3) '() q))) ===> (* 1 3))
(verify term (run* (q) (fresh (x) (term '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify term (run* (q) (fresh (x) (term '(1 * 3 * 5 * 7) '() q))) ===> (* (* (* 1 3) 5) 7)) 
(verify term (run* (q) (fresh (x) (term '(1 * 3 * 5 * 7 * 9) '() q))) ===> (* (* (* (* 1 3) 5) 7) 9))

(verify term (run* (q) (fresh (x) (term '(1 * 3 ^ 5) '() q))) ===> (* 1 (^ 3 5)))
(verify term (run* (q) (fresh (x) (term '(1 ^ 3 * 5) '() q))) ===> (* (^ 1 3) 5))

(verify term (run* (q) (fresh (x) (term q '() '(* (* 1 3) 5)))) ===> (1 * 3 * 5))
(verify term (run* (q) (fresh (x) (term q '() '(* (* (* 1 3) 5) 7)))) ===> (1 * 3 * 5 * 7))
(verify term (run* (q) (fresh (x) (term q '() '(* 1 3 5)))) =>) ; should fail
(verify term (run* (q) (fresh (x) (term q '() '(* 1 (* 3 5))))) =>) ; should fail
(verify term (run* (q) (fresh (x) (term q '() '(* 1 (* 3 (* 5 7)))))) =>) ; should fail
;(exit)

(verify term (run* (q) (fresh (x) (term '(1 / 3 / 5) '() q))) ===> (/ (/ 1 3) 5))
(verify term (run* (q) (fresh (x) (term '(1 / 3 / 5 / 7) '() q))) ===> (/ (/ (/ 1 3) 5) 7))
(verify term (run* (q) (fresh (x) (term '(1 / 3 / 5 / 7 / 9) '() q))) ===> (/ (/ (/ (/ 1 3) 5) 7) 9))

(verify term (run* (q) (fresh (x) (term q '() '(/ 1 3 5)))) =>) ; should fail
(verify term (run* (q) (fresh (x) (term q '() '(/ 1 (/ 3 5))))) =>) ; should fail
(verify term (run* (q) (fresh (x) (term q '() '(/ 1 (/ 3 (/ 5 7)))))) =>) ; should fail
(verify term (run* (q) (fresh (x) (term q '() '(/ (/ 1 3) 5)))) ===> (1 / 3 / 5))
(verify term (run* (q) (fresh (x) (term q '() '(/ (/ (/ 1 3) 5) 7)))) ===> (1 / 3 / 5 / 7))

;(verify term-todo1 (run* (q) (fresh (x) (term '(1 * 3 / 5) '() q))) ===> (/ (* 1 3) 5))
;(verify term-todo1 (run* (q) (fresh (x) (term q '() '(* 1 (/ 3 5))))) =>) ; should fail
;(verify term-todo1 (run* (q) (fresh (x) (term q '() '(/ (* 1 3) 5)))) ===> (1 * 3 / 5))

;(verify term-todo2 (run* (q) (fresh (x) (term '(1 / 3 * 5) '() q))) ===> (* (/ 1 3) 5))
;(verify term-todo2 (run* (q) (fresh (x) (term q '() '(/ 1 (* 3 5))))) =>) ; should fail
;(verify term-todo2 (run* (q) (fresh (x) (term q '() '(* (/ 1 3) 5)))) ===> (1 / 3 * 5))
;
(verify term (run* (q) (fresh (x) (term q '() '2))) ===> (2))
(verify term (run 0 (q) (fresh (x y) (term x '() y) (== q `(,x ,y)))) --->)
;(exit)

; has to be PEG because of multi-result behavior
(peg expr ;locals: (x y)
 ([_ `(+ ,x . ,y)] <=> (term x) '+ (expr `(+ . ,y)))  ; optimize associative Scheme's +
 ([_ `(+ ,x ,y)] <=> (term x) '+ (expr y))
 ([_ `(- ,x . ,y)] <=> (term x) '- (expr `(- . ,y)))  ; rely on correct variadic -
 ([_ `(- ,x ,y)] <=> (term x) '- (expr y))
 ([_ x] <=> (term x))
) 
	  
(verify expr (run* (q) (fresh (x) (expr '(1 + 3) '() q))) ===> (+ 1 3))
(verify expr (run* (q) (fresh (x) (expr '(1 + 3 + 5) '() q))) ===> (+ 1 3 5))
(verify expr (run* (q) (fresh (x) (expr '(1 * 3 + 5) '() q))) ===> (+ (* 1 3) 5))
(verify expr (run* (q) (fresh (x) (expr '(1 + 3 * 5) '() q))) ===> (+ 1 (* 3 5)))
(verify expr (run* (q) (fresh (x) (expr '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify expr (run* (q) (fresh (x) (expr '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
(verify expr (run* (q) (fresh (x) (expr '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))

(verify expr (run* (q) (fresh (x) (expr q '() '(+ 1 3)))) ===> (1 + 3))
(verify expr (run* (q) (fresh (x) (expr q '() '(+ (* 2 1) (* 3 5))))) ===> (2 * 1 + 3 * 5))
(verify expr (run* (q) (fresh (x) (expr q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))

; some syntactic sugar

(dcg Ss
 ([S 'x] <=> ε)
 ([S 'x] <=> 'a 'a (Ss 'x))
)
(dcg S
 ([S 'x] <=> ε)
 ([S 'x] <=> (: 'a 'a (S 'x)))
)

(verify S (run* (q) (S '() '() 'x)) ===> _.0)
(verify S (run* (q) (S '(b) '() 'x)) =>)
(verify S (run* (q) (S '(a) '() 'x)) =>)
(verify S (run* (q) (S '(a a) '() 'x)) ===> _.0)
(verify S (run 3 (q) (S q '() 'x)) ---> (a a a a) (a a) ()) 

(dcg A'
 ([A'] <=> ε)
 ;([A'] <=> 'a 'a)
 ([A'] <=> 'a [A'] 'a)
)
(verify A' (run* (q) (A' '() '())) ===> _.0)
(verify A' (run* (q) (A' '(a a) '())) ===> _.0)
(verify A' (run* (q) (A' '(a a a a) '())) ===> _.0)
(verify A' (run 4 (q) (A' q '())) ---> (a a a a a a) (a a a a) (a a) ())

; context-free grammar aⁿbⁿ
; more on this later
(dcg A
 ([A] <=> 'a ([A] ?) 'b)
)
(verify A.fwd (run* (q) (A '() '())) =>)
(verify A.fwd (run* (q) (A '(a a) '())) =>)
(verify A.fwd (run* (q) (A '(b a) '())) =>)
(verify A.fwd (run* (q) (A '(a b) '())) ===> _.0)
(verify A.fwd (run* (q) (A '(a a b b) '())) ===> _.0)

; for some strange reason this doesn't work in Bigloo compiler (resulting binary diverges)
(cond-expand (bigloo-eval
(verify A.bwd (run 3 (q) (A q '())) ---> (a a b b) (a b) (a a a b b b))
)(else))

(dcg B
 ([A] <=> '< ('b *) '>)
)
(verify B (run* (q) (B '(< >) '())) ===> _.0)
(verify B (run* (q) (B '(< b >) '())) ===> _.0)
(verify B (run* (q) (B '(< b b >) '())) ===> _.0)
(verify B (run* (q) (B '(< b b b >) '())) ===> _.0)
(verify B (run 4 (q) (B q '())) ---> (< >) (< b >) (< b b >) (< b b b >))

(dcg BC0
 ([BC0] <=> (('c / 'b / 'd) +))
)
(verify BC0 (run* (q) (BC0 '(< >) '())) =>)
(verify BC0 (run* (q) (BC0 '(d c a) '())) =>)
(verify BC0 (run* (q) (BC0 '(c) '())) ===> _.0)
(verify BC0 (run* (q) (BC0 '(c b) '())) ===> _.0)
(verify BC0 (run* (q) (BC0 '(d c c) '())) ===> _.0)
(verify BC0 (run 17 (q) (BC0 q '())) ---> (c) (b) (c c) (d) (c b) (b c) (c c c) (d c) (c d) (b b) (c c b) (d b) (c b c) (b c c) (c c c c) (d c c) (c d c))

(dcg BC
 ([A] <=> '< (('c / 'b / 'd) +) '>)
)
(verify BC (run* (q) (BC '(< >) '())) =>)
(verify BC (run* (q) (BC '(a) '())) =>)
(verify BC (run* (q) (BC '(< c >) '())) ===> _.0)
(verify BC (run* (q) (BC '(< c b >) '())) ===> _.0)
(verify BC (run* (q) (BC '(< d c c >) '())) ===> _.0)
(verify BC (run 17 (q) (BC q '())) ---> (< c >) (< b >) (< c c >) (< d >) (< c b >) (< b c >) (< c c c >) (< d c >) (< c d >) (< b b >) (< c c b >) (< d b >) (< c b c >) (< b c c >) (< c c c c >) (< d c c >) (< c d c >))
;(< c >) (< c c >) (< b >) (< b c >) (< d >) (< c c c >) (< d c >) (< c b >) (< b c c >) (< c b c >) (< d c c >) (< c d >) (< b b >) (< c c c c >) (< d b >) (< c d c >) (< b b c >)

(dcg test
 ([test] <=> do[(begin (write 'zap!)) #s]
      'x)
)

(def mtest test)

(let-syntax ([mtest mtest])
(dcg foo
 ([foo] <=> [mtest])
 ([foo] <=> [mtest] 'and [mtest])
 ([foo] <=> [mtest] 'and [mtest] 'and [mtest])
))

(begin (define eff.1 (with-output-to-string (fn =>
   (verify foo.1 (run* (q) (foo '(x) '())) ===> _.0))))
   ;(verify foo-eff.1 (length (string-split eff.1 "!")) = 1)
   ;(newline)
   )

;(run* (q) (foo '(x and x) '()))
;(run* (q) (foo '(x and x and x) '()))
(begin (define eff.2 (with-output-to-string (fn =>
   (verify foo.2 (run* (q) (foo '(x and x and x) '())) ===> _.0))))
   ;(verify foo-eff.2 (length (string-split eff.2 "!")) = 3)
   (newline)
   )

;(pp (test count:))
(begin (define eff.r (with-output-to-string (fn =>
   (verify foo.r (run 4 (q) (foo q '())) ---> (x) (x and x) (x and x and x)))))
   ;(verify foo-eff.r (length (string-split eff.r "!")) = 3)
   ;(newline)
   )

;(pp (test count:))(test reset:)
;(exit)

; left-factoring
;(dcg baz ([_] <=> epsilon) ([_] <=> 'and [test]))
;(dcg quux ([_] <=> epsilon) ([_] <=> ('and [test] [baz])))
;(dcg bar'([_] <=> [test] [quux]))
(dcg bar
 ([bar] <=> [test] ((: 'and [test] ((: 'and [test]) / ε)) / ε))
)
(begin (define eff.3 (with-output-to-string (fn =>
       (verify bar (run* (q) (bar '(x) '())) ===> _.0))))
       ;(verify bar-eff (length (string-split eff.3 "!")) = 1)
       ;(newline)
       )
;(run* (q) (bar '(x and x) '()))
(begin (define eff.4 (with-output-to-string (fn =>
   (verify bar (run* (q) (bar '(x and x and x) '())) ===> _.0))))
   ;(verify bar-eff (length (string-split eff.4 "!")) = 3)
   ;(newline)
   )

(begin (define eff.5 (with-output-to-string (fn =>
   (verify bar (run 4 (q) (bar q '())) ---> (x and x and x) (x) (x and x)))))
   ;(verify bar-eff (length (string-split eff.5 "!")) = 3)
   ;(newline)
   )

; solving left-recursion by the "trick"
(dcg SS ;locals: (x)
 ([X 'z] <=> ε)
 ([_ `(S ,x)] <=> [SS x] 'a 'a)
)
(def X SS)

(verify SS.zero (run* (q) (X '() '() q)) ===> z)
(verify SS.fwd (run* (q) (X '(a a) '() q)) ===> (S z))
(verify SS.prefix (run* (q) (fresh (_ r) (X '(a a a a) _ r) (== q `(,_ ,r)))) ---> ((a a a a) z) ((a a) (S z)) (() (S (S z))))
(verify SS.fwd (run* (q) (X '(a a a a) '() q)) ===> (S (S z)))
(verify SS.fwd (run* (q) (X '(a a a a a a) '() q)) ===> (S (S (S z))))
(verify SS.rev (run* (q) (X q '() 'z)) ===> ())
(verify SS.rev (run* (q) (X q '() '(S z))) ===> (a a))
(verify SS.rev (run* (q) (X q '() '(S (S z)))) ===> (a a a a))
(verify SS.fail (run* (q) (X '(a) '() q)) =>)
(verify SS.fail (run* (q) (X '(a a a) '() q)) =>)
(verify SS.fail (run* (q) (X '(a a a a a) '() q)) =>)
(verify SS.fail (run* (q) (X q '() 'x)) =>)
(verify SS.fail (run* (q) (X q '() '(S x))) =>)
(verify SS.fail (run* (q) (X q '() '(S (S x)))) =>)
(verify SS.enum (run 3 (q) (fresh (x y) (X x '() y) (== q `(,x ,y)))) ---> (() z) ((a a) (S z)) ((a a a a) (S (S z))))

; generate infinite stream of fresh variables
(def (freshº x)
  (conde ([== x '()])
     (else (fresh (y z)
      (freshº z)
      (== x `(,y . ,z))
      ))
     ))

(verify freshº (run 4 (q) (freshº q)) ---> (_.0 _.1 _.2) (_.0 _.1) (_.0) ())

(def (prefixº a b)
   (fresh (x)
      (freshº x)
      (appendo a x b)
      ;(appendo a `(fin . ,x) b)
      ))

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
; 
; Hutton's razor with exponents
; left-factoring, complete, but not reversible since the bottom is never reached
; can not use full inference here because of inherited "attributes", e.g., [[x]]
(defn exprs (dcg <=: expr
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
(verify exprs.expr (run* (q) (exprs '(2 + 3 + xx) '() q)) =>)
(verify exprs.expr (run* (q) (fresh (x) (exprs '(2 ^ 2 * 1 + 3 * 5) '() q))) ===> (+ (* (^ 2 2) 1) (* 3 5)))
(verify exprs.expr (run* (q) (fresh (x) (exprs '(1 * 2 + 3 * 5) '() q))) ===> (+ (* 1 2) (* 3 5)))
;(verify exprs.expr (run 1 (q) (fresh (x) (exprs q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))

; Correct associativity for operators,
; no need to do left-recursion elimination
; still need to do separation into sub-goals to solve precedence
; Need to put the base case at the end because of
; potential immediate mutual infinite descent

; non-encapsulated version for better testing
; defaults to bidirectional, complete
(dcg
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
))

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
(verify Factor (run* (q) (fresh (X) (Factor q X '(^ 3 4)))) ===> ( 3 ^ 4 . _.0))

(verify Factor (run* (q) (Factor q '() '(^ (^ 3 4) (^ 5 6)))) =>)

(verify Term (run* (q) (fresh (x) (Term '(1 * 3) '() q))) ===> (* 1 3))
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5) '() q))) ===> (* (* 1 3) 5))
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5 * 7) '() q))) ===> (* (* (* 1 3) 5) 7)) 
(verify Term (run* (q) (fresh (x) (Term '(1 * 3 * 5 * 7 * 9) '() q))) ===> (* (* (* (* 1 3) 5) 7) 9))

(verify Term (run* (q) (fresh (x) (Term '(1 * 3 ^ 5) '() q))) ===> (* 1 (^ 3 5)))
(verify Term (run* (q) (fresh (x) (Term '(1 ^ 3 * 5) '() q))) ===> (* (^ 1 3) 5))

(verify Term (run* (q) (fresh (x) (Term q '() '(* (* 1 3) 5)))) ===> (1 * 3 * 5))
(verify Term (run* (q) (fresh (x) (Term q '() '(* (* (* 1 3) 5) 7)))) ===> (1 * 3 * 5 * 7))
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 3 5)))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 (* 3 5))))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(* 1 (* 3 (* 5 7)))))) =>) ; should fail
;(exit)

(verify Term (run* (q) (fresh (x) (Term '(1 / 3 / 5) '() q))) ===> (/ (/ 1 3) 5))
(verify Term (run* (q) (fresh (x) (Term '(1 / 3 / 5 / 7) '() q))) ===> (/ (/ (/ 1 3) 5) 7))
(verify Term (run* (q) (fresh (x) (Term '(1 / 3 / 5 / 7 / 9) '() q))) ===> (/ (/ (/ (/ 1 3) 5) 7) 9))

(verify Term (run* (q) (fresh (x) (Term q '() '(/ 1 3 5)))) =>) ; should fail
(verify Term (run* (q) (fresh (x) (Term q '() '(/ 1 (/ 3 5))))) =>) ; should fail
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
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ (+ 1 3) 5)))) ===> (1 + 3 + 5))
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ 1 (+ 3 5))))) =>)
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ (* 2 1) (* 3 5))))) ===> (2 * 1 + 3 * 5))
(verify Expr (run* (q) (fresh (x) (Expr q '() '(+ (* 2 a) (* x 5))))) ===> (2 * a + x * 5))

(verify Expr (run* (q) (fresh (x) (Expr '(3) '() q))) ===> 3)

(defn ife (peg <=> if
(if ;locals: (x y z)
 ([_ `(if ,x ,y ,z)] <=> 'if [Expr x] 'then [Expr y] 'else [Expr z])
 ([_ `(if ,x ,y #f)] <=> 'if [Expr x] 'then [Expr y])
 ([_ `(if ,x ,y ,z)] <=> 'if [Expr x] 'then [if y] 'else [Expr z])
 ([_ `(if ,x ,y #f)] <=> 'if [Expr x] 'then [if y])
)))

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

; for some strange reason this does not work with Bigloo compiler (Globalizer diverges)	      
(cond-expand (bigloo-eval
; encapsulate internal goals
; bidirectional, complete (halts on no parse) and no sideways
(defn hutton (dcg <=> Expr
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

(defn ifo (peg <=> if
(if ;locals: (x y z)
 ([_ `(if ,x ,y ,z)] <=> 'if [hutton x] 'then [hutton y] 'else [hutton z])
 ([_ `(if ,x ,y #f)] <=> 'if [hutton x] 'then [hutton y])
 ([_ `(if ,x ,y ,z)] <=> 'if [hutton x] 'then [if y] 'else [hutton z])
 ([_ `(if ,x ,y #f)] <=> 'if [hutton x] 'then [if y])
)))

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
)(else))

; for some strange reason this does not work with Bigloo compiler (Globalizer diverges)
(cond-expand (bigloo-eval
; add sideways, starts to lean left, so incomplete (diverges on no parse), but can generate all pairs
(def hutton' (dcg => Expr
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
 ((a) a) ((a + a) (+ a a)) ((a * a) (* a a)) ((0) 0) ((a ^ a) (^ a a)) ((a - a) (- a a)) ((0 + a) (+ 0 a)) ((b) b) ((b + a) (+ b a)) ((1) 1)
;((a) a) ((a + a) (+ a a)) ((a * a) (* a a)) ((a ^ a) (^ a a)) ((0) 0) ((a - a) (- a a)) ((b) b) ((0 + a) (+ 0 a)) ((a / a) (/ a a)) ((a + a * a) (+ a (* a a)))
;((a) a) ((a + a) (+ a a)) ((0) 0) ((a * a) (* a a)) ((b) b) ((a ^ a) (^ a a)) ((a - a) (- a a)) ((0 + a) (+ 0 a)) ((1) 1) ((b + a) (+ b a))
)

;;this is the price we pay for handling bidirectionality in a nice way (run*, not run(N))
(verify hutton'.s2
(parameterize ([*digits* '(42)] [*letters* '(#\x)])
(run 10 (q) (fresh (x y) (hutton' x  '()  y) (== q `(,x ,y))))
) --->
((x + x) (+ x x)) ((x) x) ((42 + x) (+ 42 x)) ((x * x) (* x x)) ((x ^ x) (^ x x)) ((x + x * x) (+ x (* x x))) ((x - x) (- x x)) ((42) 42) ((42 + x * x) (+ 42 (* x x))) ((42 - x) (- 42 x))
;((x) x) ((x + x) (+ x x)) ((x * x) (* x x)) ((42) 42) ((42 + x) (+ 42 x)) ((x - x) (- x x)) ((x ^ x) (^ x x)) ((x + x * x) (+ x (* x x))) ((x / x) (/ x x)) ((42 - x) (- 42 x))
)

(cond-expand (disable
(parameterize ([*digits* '(42)] [*letters* '(#\x)])
(run 40 (q) (fresh (x y) (hutton' x  '()  y) (== q `(,x ,y))))
))(else 'takes-too-long))

)(else))

; immediate infinite self-recursion
(dcg BB ;locals: (b)
   ([_ `(B ,b)] <=> [BB b])
)

; example from [[http://okmij.org/ftp/Haskell/LeftRecursion.hs]]
; S -> S A C | C
; A -> B | aCa
; B -> B
; C -> b | C A
(defn gram (dcg => S
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
(verify gram (run 7 (q) (fresh (x y) (gram x '() y) (== q x))) ---> (b) (b a b a b) (b a b a) (b a b a b a a b) (b a b a b a a) (b a b a b a b a) (b a b a a b a))

;; nested parsers (explicit version)
(dcg N ;locals: (x)
   ([_] <=> 'x)
   ([_ `(N ,x)] <=> '< (N x) '>))

(verify N.fail (run* (q) (N '() '() q)) =>)
(verify N.sing (run* (q) (N '(x) '() q)) ===> x)
(verify N.wrap (run* (q) (N '(< x >) '() q)) ===> (N x))
(verify N.dwra (run* (q) (N '(< < x > >) '() q)) ===> (N (N x)))
(verify N.rev.fail (run* (q) (N q '() '())) =>)
(verify N.rev.sing (run* (q) (N q '() 'x)) ===> (x))
(verify N.rev.wrap (run* (q) (N q '() '(N x))) ===> (< x >))
(verify N.rev.drwap (run* (q) (N q '() '(N (N x)))) ===> (< < x > >))
(verify N.enum (run 5 (q) (fresh (x y) (N x '() y) (== q x))) ---> (x) (< x >) (< < x > >) (< < < x > > > ) (< < < < x > > > > ))

;; testing un-quasiquote
(dcg P ;locals: (x)
   ([_] <=> 'x)
   ([_ `(P ,x)] <=> ;do[(trace-vars 'p (x))]
		`(a ,(P x) b) 'E))

(verify P (run* (q) (P '((a b) E) '() q)) =>)
(verify P (run* (q) (P q '() '())) =>)
(verify P (run* (q) (P '((a x b) E) '() q)) ===> (P x))
(verify P (run* (q) (P q '() '(P x))) ===> ((a x b) E))
(verify P (run* (q) (P '((a (a x b) E b) E) '() q)) ===> (P (P x)))
(verify P (run* (q) (P q '() '(P (P x)))) ===> ((a (a x b) E b) E))
(verify P (run 5 (q) (fresh (x y) (P x '() y) (== q y))) ---> x (P x) (P (P x)) (P (P (P x))) (P (P (P (P x)))))

;; nested parsers (piggybacking on Scheme's reader)
(dcg PP ;locals: (x)
   ([_] <=> 'x)
   ([_ `(PP ,x)] <=> `(,[PP x]))
)

(verify PP (run* (q) (PP '() '() q)) =>)
(verify PP (run* (q) (PP q '() '())) =>)
(verify PP (run* (q) (PP '(x) '() q)) ===> x)
(verify PP (run* (q) (PP q '() 'x)) ===> (x))
(verify PP (run* (q) (PP '([x]) '() q)) ===> (PP x))
(verify PP (run* (q) (PP q '() '(PP x))) ===> ([x]))
(verify PP (run* (q) (PP '([[x]]) '() q)) ===> (PP (PP x)))
(verify PP (run* (q) (PP q '() '(PP (PP x)))) ===> ([[x]]))
(verify PP (run 5 (q) (fresh (x y) (PP x '() y) (== q x))) ---> (x) ((x)) (((x))) ((((x)))) (((((x))))))

(dcg Q ;locals: (x)
   ([_] <=> 'x)
   ([_ `(Q1 ,x)] <=> `(a ,[Q x] `b))
   ([_ `(Q2 ,x)] <=> `(c ,`(d ,[Q x] 'e) f))
   ([_ `(Q3 ,x)] <=> `(g ,`(,[Q x]) h))
   ;XXX TODO([_ `(Q ,x)] <=> `(a `(b ,,(Q x) c) d) 'E) 
)

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

; S -> x S x | x should not work for Packrat (according to Wikipedia). Still,
; it is context free.
; maybe a hint that our parser is not strictly packrat (i.e., linear time),
; but more general type-1 (i.e., exponential) e.g., CYK,
; or even type-0 (turing-complete). Most likely, type-0 since its equivalent
; to attribute grammars
(defn s (dcg <=> S
 (S
   ([_] <=> 'x)
   ([_ `(s ,x)] <=> 'x [S x] 'x)
   )
)) 

(verify s (run* (q) (s '() '() q)) =>)
(verify s (run* (q) (s '(y) '() q)) =>)
(verify s (run* (q) (s '(x) '() q)) ===> x)
(verify s (run* (q) (s '(x x x) '() q)) ===> (s x))
(verify s (run* (q) (s q '() '())) =>)
(verify s (run* (q) (s q '() 'y)) =>)
(verify s (run* (q) (s q '() 'x)) ===> (x))
(verify s (run* (q) (s q '() '(s x))) ===> (x x x))
(verify s.enum (run 3 (q) (fresh (x y) (s x '() y) (== q x))) ---> (x) (x x x) (x x x x x))

; higher-order rules
(defn [comma p] (dcg => c
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
(dcg a ([_] <=> 'a))
(dcg b ([_] <=> 'b))

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

; reversible aⁿbⁿ (we can count!)
; the _ automatically ensures that we only use vars declared in the head,
; i.e., if used in the body then it must be declared in the head
(defn anbn (dcg <=> a
 (a ([_ `(S ,x)] <=> 'a ([a x] ?) 'b))
 ))

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

(dcg aa ([] <=> 'a))
(dcg bb ([] <=> 'a 'b))

(run* (q) (aa '(a) '() q))
(run* (q) (aa '(b) '() q))
(run* (q) (bb '(a b) '() q))
(run* (q) (bb '(b a) '() q))

; a grammar from Mercury paper, we know left-recursion won't hurt
(defn merc (dcg <=: a
 (a ([_ `(a ,x)] <=> ([b x] / [c x])))
 (b ([_ `(b ,x)] <=> 'x [d x] 'y))
 (c ([_ `(c ,x)] <=> 'x [d x] 'z))
 (d ([_ `(d ,x)] <=> ([a x] / ε)))
 ))

(verify merc (run* (q) (merc '(x x x z z z) '() q)) ---> (a (c (d (a (c (d (a (c (d _.0))))))))))

(dcg ;<=> Expr
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
);)

(verify Factor' ([first (run* (q) (fresh (X) (Factor' '(2 a 3) X q)))] '()) === 2)
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3) '() q))] '()) === '(^ 2 3))
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3 ^ 4) '() q))] '()) === '(^ (^ 2 3) 4))
(verify Factor' ([first (run* (q) (Factor' '(2 ^ 3 ^ 4 ^ 5) '() q))] '()) === '(^ (^ (^ 2 3) 4) 5))
;(verify Factor' ([(first (run* (q) (Term' '(2 ^ 3) '() q))) '()] '()) === '(^ 2 3))
;(verify Factor ([(first (run* (q) (Term '(2 * 3) '() q))) '()] '()) === '(* 2 3))

; non context-free grammar aⁿbⁿcⁿ
; S ← &(A 'c') 'a'+ B !('a'/'b'/'c')
; A ← 'a' A? 'b'
; B ← 'b' B? 'c'
(def aⁿbⁿcⁿ (dcg <=> S
  (S ([S] <=> when([A] 'c) ('a +) [B] unless(['a / 'b / 'c])))
  (A ([A] <=> 'a ([A] ?) 'b))
  (B ([B] <=> 'b ([B] ?) 'c))
  ))

(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '() '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a b c) '())) ===> _.0)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b b c c) '())) ===> _.0)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b b c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a b c c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a b b c c) '())) =>)
(verify aⁿbⁿcⁿ (run* (q) (aⁿbⁿcⁿ '(a a a b b b c c c) '())) ===> _.0)

; for some strange reason this doesn't work in Bigloo compiler (resulting binary diverges)
(cond-expand (bigloo-eval
(verify aⁿbⁿcⁿ (run 3 (q) (aⁿbⁿcⁿ q '())) ---> (a b c . _.0) (a a b b c c . _.0) (a a a b b b c c c . _.0))
)(else))

(def Λ (dcg <=: S
  (L ([_ `(lambda (,x) ,y)] <=> 'λ [T x] '· [S y]))
  ;(A ([_ `(,x ,y)] <=> ([S y] +)))
  ;(A ([_ `(,x . ,y)] <=> `(,[S x] ,([S y] *) !)))
  (A ([_ x] <=> `(! ,([S x] +)))
     ([_ x] <=> '! ([S x] +)))
  (T ([_ x] <=> [symbol x]))
  (S ([_ x] <=> ([L x] / [A x] / [T x])))
  ))

(verify Λ (run* (q) (Λ '() '() q)) =>)
(verify Λ (run* (q) (Λ '(x) '() q)) ===> x)
(verify Λ (run* (q) (Λ '(! x) '() q)) ===> (x))
(verify Λ (run* (q) (Λ '(! x y) '() q)) ===> (x y))
(verify Λ (run* (q) (Λ '(! x y z) '() q)) ===> (x y z))
(verify Λ (run* (q) (Λ '(! x y z w) '() q)) ===> (x y z w))
(verify Λ (run* (q) (Λ '(! (! x y) z ) '() q)) ===> ((x y) z))
(verify Λ (run* (q) (Λ '(λ|x|· y) '() q)) ===> (lambda (x) y))
(verify Λ (run* (q) (Λ '(λ|x|· ! x y) '() q)) ===> (lambda (x) (x y)))
(verify Λ (run* (q) (Λ '(λ|x|· λ|y|· ! x y) '() q)) ===> (lambda (x) (lambda (y) (x y))))

; the end