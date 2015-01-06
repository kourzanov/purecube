(module Parse-json
   (library bkanren slib)
   (import (helpers "helpers.scm")
	   (loprog "loprog.sch")
	   (Parse "Parse.scm")
	   (hacks "hack-syntax.sch")
   ;(main main)
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

(defn [json-ne-list elem] (pcg heads: (reu: elem)
  ([_ '()] <=> ε)
  ([_ `(,v . ,vs)] <=>
   [elem v] [(: |,| [elem vs]) *])
 ))

(def [ne-list-tests]
   (verify ne-list0 (run* (q) ([json-ne-list symbol] '() '() q)) ===> ())
   (verify ne-list1 (run* (q) ([json-ne-list symbol] '(a) '() q)) ===> (a))
   (verify ne-list2 (run* (q) ([json-ne-list symbol] '(a |,| b) '() q)) ===> (a b))
   (verify ne-list2 (run* (q) ([json-ne-list symbol] '(a |,| b |,| c) '() q)) ===> (a b c))
   (verify ne-list0.rev (run* (q) ([json-ne-list symbol] q '() '())) ===> ())
   ;(verify ne-list1.rev (run* (q) ([json-ne-list symbol] q '() '(a))) ===> (a))
   ;(verify ne-list2.rev (run* (q) ([json-ne-list symbol] q '() '(a b))) ===> (a |,| b))
)

(defn [json-non-empty-list elem] (pcg <=> s
 (s ([_ `(,v)] <=> [elem v])
    ([_ `(,v . ,vs)] <=> [elem v] |,| [s vs])
 )))

(defn [jason-non-empty-list comma elem] (pcg <=> s
 (s ([_ `(,v)] <=> [elem v])
    ([_ `(,v . ,vs)] <=> [elem v] [idem comma] [s vs])
 )))

; needs to be external since its needed for extensibility
(pcg (json-bool ([_] <=> (true / false))))

(pcg
 (json-symbol extend: extend ([_ x] <=> [strings x]))
 ;(json-number ([_ x] <=> [number x]))
 ;(json-symbol = strings)
 (json-number = number)
 (json-value ([_] <=> null)
  ([_ x] <=> [json-bool x])
  ([_ x] <=> ([json-symbol x] / [json-number x]))
  ([_ x] <=> ([json-object x] / [json-array x]))
 )
 ;(mjson-value = [memo json-value])
 (mjson-value = json-value)
 (json-pair ([_ `(,n . ,v)] <=> [json-symbol n] |:| [mjson-value v]))
 (json-value-list ([_ '()] <=> ε)
  ([_ l] <=> [(jason-non-empty-list '|,| mjson-value) l]))
 (json-pair-list ([_ '()] <=> ε)
  ([_ l] <=> [(jason-non-empty-list '|,| json-pair) l]))
 (json-array
  ([_ `(arr . ,es)] <=> |[| [json-value-list es] |]|))
 (json-object
  ([_ `(obj . ,es)] <=> |{| [json-pair-list es] |}|))
)

(def json-ext (let ([extend' (extend)])
  (fn-with [apply extend'] || 'json-symbol => 
     ;(pcg ([_ x] <=> [symbol x]))
     symbol
  )))

(def [json-tests]
(verify json-array0 (run* (q) (json-value
      '#h:[]
      '() q))
      ===> [arr]
   )
(verify json-array1 (run* (q) (json-value
      '#h:[true, false]
      '() q))
      ===> [arr true false]
   )
(verify json-array1.rev (run* (q) (json-value
  q
  '() '[arr true false]))
   ===> (|[| true |,| false |]|)
   )
(verify json-object0 (run* (q) (json-value
      '#h:{}
      '() q))
      ===> [obj]
   )
(verify json-object1 (run* (q) (json-value
      '#h:{"a":"b"}
      '() q))
      ===> [obj ("a" . "b")]
   )
(verify json-object1.rev (run* (q) (json-value
   q
   '() '[obj ("a" . "b")]))
   ===> (|{| "a" |:| "b" |}|)
   )
(verify json-value1 (run* (q) (json-value
      '#h:{"a":["b",2.3]}
      '() q))
      ===> [obj ("a" . (arr "b" 2.3))]
   )
(parameterize ([extend json-ext])
   ;[mjson-value reset: 0] [mjson-value reset: 1]
   (verify json-value1.ext (run* (q) (json-value
      '#h:{ a: ["b",2.3],c:d}
      '() q))
      ===> [obj (a . (arr "b" 2.3)) (c . d)]
   )
   (verify json-value1.ext.rev (run* (q) (json-value
      q
      '() '[obj (a . (arr "b" 2.3))]))
      ===> (|{| a |:| |[| "b" |,| 2.3 |]| |}|)
   ))
)

; low-level non-terminals
(pcg
(wss ([] <=> (#\newline / #\tab / #\space / #\return / #\010 / #\014)))
(ctr ([] <=> (#\" / #\[ / #\] / #\{ / #\} / #\, / #\:)))
(ws condo: condu ; eager processing
   ([] <=> ε [wss] [ws])
   ([] <=> ε))
(1-9 ([_] <=> (#\1 / #\2 / #\3 / #\4 / #\5 / #\6 / #\7 / #\8 / #\9)))
(0-9 ([_] <=> (#\0 / #\1 / #\2 / #\3 / #\4 / #\5 / #\6 / #\7 / #\8 / #\9)))
(hex ([_] <=> (#\a / #\b / #\c / #\d / #\e / #\f))
     ([_] <=> (#\A / #\B / #\C / #\D / #\E / #\F))
     ([_ x] <=> [0-9 x]))
(esc ([_] <=> #\")
     ([_] <=> #\\)
     ([_] <=> #\/)
     ([_ #\010] <=> #\b)
     ([_ #\014] <=> #\f)
     ([_ #\newline] <=> #\n)
     ([_ #\return] <=> #\r)
     ([_ #\tab] <=> #\t))
(jason-str-char1 condo: condu
 ([_ x] <=> #\\ [esc x])
 ([_ π(integer->ucs2 (string->integer (list->string a) 16))] <=>
   #\\ #\u ([hex a] * 3 4))
 ([_ x] <=> unless[(#\" / #\\)] [idem x]))
(jason-str-char condo: condu
 ([_ x] <=> #\\ [esc x])
 ([_ π(integer->ucs2 (string->integer (list->string (list a b c d)) 16))] <=>
   #\\ #\u [hex a] [hex b] [hex c] [hex d])
 ([_ x] <=> unless[(#\" / #\\)] [idem x]))
(jason-sym-first-char condo: condu
 ([_ x] <=> ε unless[([wss] / [ctr] / [0-9 x])] [idem x]))
(jason-sym-char condo: condu
 ([_ x] <=> ε unless[([wss] / [ctr])] [idem x]))
(jason-sym
 ([_ π(string->symbol (list->string `(,x . ,xs)))] <=> [jason-sym-first-char x] ([jason-sym-char xs] *)))
(jason-string
 ([_ π(list->string x)] <=> #\" ([jason-str-char x] *) #\"))
;(jason-number locals: (x xs) ([_ π 42] <=> (#\- ?) (#\0 / (: [1-9 x] ([0-9 xs] *)))))
(jason-natural
 ([_ π(+ (* x 10) (- (char->integer y) 48))] <=> [jason-natural x] [0-9 y])
 ([_ π(- (char->integer x) 48)] <=> [1-9 x]))
(jason-nat
 ([_ 0] <=> #\0)
 ([_ x] <=> [jason-natural x]))
(jason-integer
 ([_ x] <=> (#\+ ?) [jason-nat x])
 ([_ π(- x)] <=> #\- [jason-nat x])
 ;([_ x] <=> [jason-nat x])
 )
(jason-frac
 ;([_ 0] <=> ε) ; not present in official Json
 ([_ π(/ (- (char->integer x) 48) 10)] <=> ε [0-9 x])
 ([_ π(/ (+ (- (char->integer x) 48) y) 10)] <=> ε [0-9 x] [jason-frac y]))
(jason-float
 ([_ x] <=> #\+ [jason-float x])
 ([_ π(- x)] <=> #\- [jason-float x])
 ([_ x] <=> [jason-nat x])
 ([_ π(+ x y)] <=> [jason-nat x] #\. [jason-frac y]))
(jason-num
 ([_ π(* x (^ 10 y))] <=> [jason-float x] (#\e / #\E) [jason-integer y])
 ([_ x] <=> [jason-float x])
 )
)

; .123 123/1000 (100+20+3)/1000 1/10+2/100+3/1000 ((3/10+2)/10+1)/10

(pcg
 (jason-symbol extend: extend ([_ x] <=> [ws] [jason-string x] [ws]))
 (jason-symb ([_ x] <=> [ws] [jason-sym x] [ws]))
 (jason-number ([_ x] <=> [ws] [jason-num x] [ws]))
 (jason-value
  ([_ x] <=> [ws] ([chars 'true x] / [chars 'false x] / [chars 'null x]) [ws])
  ([_ x] <=> ([jason-symbol x] / [jason-number x]))
  ([_ x] <=> ([jason-object x] / [jason-array x]))
 )
 (jason-pair ([_ `(,n . ,v)] <=> [jason-symbol n] #\: [jason-value v]))
 (jason-value-list ([_ '()] <=> ε)
  ([_ l] <=> [ws] [(jason-non-empty-list #\, jason-value) l] [ws]))
 (jason-pair-list ([_ '()] <=> ε)
  ([_ l] <=> [ws] [(jason-non-empty-list #\, jason-pair) l] [ws]))
 (jason-array
  ([_ `(arr . ,es)] <=> [ws] #\[ [jason-value-list es] #\] [ws]))
 (jason-object
  ([_ `(obj . ,es)] <=> [ws] #\{ [jason-pair-list es] #\} [ws]))
)

(def jason-ext (let ([extend' (extend)])
  (fn-with [apply extend'] || 'jason-symbol =>
     ;(pcg ([_ x] <=> [ws] [jason-sym x] [ws]))
     jason-symb
  )))

(def [jason-tests]
   (pp (run* (q) (jason-str-char '(#\\ #\n) '() q)))
   (pp (run* (q) (jason-str-char '(#\\ #\u #\0 #\3 #\C #\0) '() q)))
   (pp (run* (q) (jason-str-char1 (string->list "\\u03c01") '(#\1) q)))
   (pp (run* (q) (jason-str-char '(#\X) '() q)))
   (pp (run* (q) (jason-str-char '(#\") '() q)))
   (pp (run* (q) (jason-str-char '(#\\) '() q)))
   (pp (run* (q) (jason-string '(#\" #\a #\b #\c #\") '() q)))
   (pp (run* (q) (jason-string (string->list "\"a\\b\\\"cd\"") '() q)))
   (pp (run* (q) (jason-number '(#\0) '() q)))
   (pp (run* (q) (jason-number '(#\7) '() q)))
   (pp (run* (q) (jason-number '(#\7 #\0 #\9) '() q)))
   (pp (run* (q) (jason-number '(#\7 #\. #\0 #\9) '() q)))
   (pp (run* (q) (jason-number '(#\9 #\3) '() q)))
   (pp (run* (q) (jason-number '(#\- #\9 #\3) '() q)))
   (pp (run* (q) (jason-number '(#\- #\9 #\. #\3) '() q)))
   (pp (run* (q) (jason-number '(#\3 #\. #\1 #\4 #\e #\+ #\2) '() q)))
   (pp (run* (q) (jason-number '(#\3 #\. #\1 #\4 #\E #\2) '() q)))
   (pp (run* (q) (jason-number '(#\- #\3 #\1 #\4 #\e #\- #\2) '() q)))
   (pp (run* (q) (jason-symb (string->list "abcd ") '() q)))

   (verify jason-value1 (run* (q) (jason-value
      '#x: { "a": ["b",2.3 ]} 
      '() q))
      ===> [obj ("a" . (arr "b" 2.3))]
   )
   (verify jason-value3 (run* (q) (jason-value
      '#x: { "a": ["b",2.3,true]} 
      '() q))
      ===> [obj ("a" . (arr "b" 2.3 true))]
   )
(parameterize ([extend jason-ext])
   (verify jason-value1.ext (run* (q) (jason-value
      '#x: { a: ["b",2.3 ]} 
      '() q))
      ===> [obj (a . (arr "b" 2.3))]
   ))
(parameterize ([extend jason-ext])
   (verify jason-value2.ext (run* (q) (jason-value
      '#x: { a: [b,2.3 ]} 
      '() q))
      ===> [obj (a . (arr b 2.3))]
   ))
)

(def [bench-tests]
   (let ([data (call-with-input-file "test.json" hack-read)])
      ;(pp data)
      (pp (length data))
      ;(printf "Hits: ~a/~a~n" [mjson-value hits: 0] [mjson-value hits: 1])
      (pp (run* (q) (json-value data '() q)))
      ;(pp (run* (q) (mjson-value data '() q)))
      ;(printf "Hits: ~a/~a~n" [mjson-value hits: 0] [mjson-value hits: 1])
      ))

(def inserto (predicate
 ([_ e l `(,e . ,l)])
 ([_ e `(,h . ,t) `(,h . ,r)] :- [inserto e t r])
))

(def memberᵒ (predicate
 ([_ e `()] :- #u)
 ;([_ e `(,e . ,t)])
 ;([_ e `(,h . ,t)] :- ([== e h] / (: [! == e h] [membero e t])))
 ([_ e `(,h . ,t)] :- ([== e h] / [memberᵒ e t]))
))

(def extendo' (predicate ;condo: condu
 ; ([_ t ts' ts] :- [trace-vars 'extendo (t ts' ts)]
 ;    ((: [membero t ts'] [== ts ts']) / [inserto t ts' ts]))
 ([_ t ts ts] :- [membero t ts])
 ([_ t ts' ts] :- [! membero t ts'] [inserto t ts' ts])
))

(def extendo (predicate
 ([_ t ts' ts] :- ([membero t ts'] *-> [== ts' ts] / [inserto t ts' ts]))
))

(def [inserto-tests]
   (verify membero (run* (_) (membero 'x '(1 2 x 3))) ===> _.0)
   (verify membero (run* (_) (membero 'x '(1 x 2 x 3))) ===> _.0 _.0)
   ;(verify membero (run* (_) (membero 'x '(1 x 2 x 3))) ===> _.0)
   ;(verify membero (run* (_) (membero 'x '(1 2 3))) =>)
   (verify membero (run* (x) (membero x '(1 2 3))) ===> 1 2 3)
   (verify membero (run* (x) (membero x '(1 1 2 3))) ===> 1 1 2 3)
   ;(verify membero (run* (x) (membero x '(1 2 3))) ===> 1)
   ;(verify membero (run* (x) (membero x '(1 1 2 3))) ===> 1)
   (verify membero (run 5 (x) (membero 'x x)) ---> (x . _.0) (_.0 x . _.1) (_.0 _.1 x . _.2) (_.0 _.1 _.2 x . _.3) (_.0 _.1 _.2 _.3 x . _.4))
   ;(verify membero (run 5 (x) (membero 'x x)) ---> (x . _.0))
   
   (verify inserto (run* (r) (inserto 'x r '(1 2 3))) =>)
   (verify inserto (run* (r) (inserto 'x r '(x 2 3))) ===> (2 3))
   (verify inserto (run* (r) (inserto 'x r '(1 x 3))) ===> (1 3))
   (verify inserto (run* (r) (inserto 'x r '(1 2 x))) ===> (1 2))
   (verify inserto (run* (r) (inserto 'x '(1 2 3) r)) ---> (x 1 2 3) (1 x 2 3) (1 2 x 3) (1 2 3 x))
   ;(verify inserto (run* (r) (inserto 'x '(x 1 2 3) r)) ---> (x 1 2 3) (1 x 2 3) (1 2 x 3) (1 2 3 x))
   (verify inserto (run* (r) (fresh (x) (inserto r x '()))) =>)
   (verify inserto (run* (r) (fresh (x) (inserto x r '(1 2 3)))) ---> (2 3) (1 3) (1 2))
   (verify inserto (run* (r) (fresh (x) (inserto r x '(1 2 3)))) ---> 1 2 3)
   (verify inserto (run* (r) (inserto r '(1 2 3) '(1 2 4))) =>)
   (verify inserto (run* (r) (inserto r '(1 2 3) '(1 2 x 3))) ===> x)

   (verify extendo (run* (r) (extendo 'x '(1 2 3) r)) ---> (x 1 2 3) (1 x 2 3) (1 2 x 3) (1 2 3 x));(x 1 2 3))
   (verify extendo (run* (r) (extendo 'x '(1 x 2 3) r)) ---> (1 x 2 3))
)

(defn sigma' (predicate ;condo: condu
 ([_ t `(Union . ,ts) `(Union . ,ts)] :- [membero t ts])
 ([_ t `(Union . ,ts') `(Union . ,ts)] :- [! membero t ts'] [inserto t ts' ts])
 ([_ t t' t'] :- [== t t'])
 ([_ t t' `(Union . ,ts)] :- [! == t t'] [inserto t `(,t') ts])
))

(defn sigma (predicate locals: (ts')
 ([_ t `(Union . ,ts') `(Union . ,ts)] :- ([membero t ts'] *-> [== ts' ts] / [inserto t ts' ts]))
 ([_ t t' ts] :- ([== t t'] *-> [== t' ts] / ([! carᵒ t' 'Union] : [== ts `(Union . ,ts')] : [inserto t `(,t') ts'])))
))

(defn [tjason-non-empty-list comma elem] (pcg <=> s
 (s locals: (t ts')
  ([_ `(,v) t] <=> [elem v t])
  ([_ `(,v . ,vs) ts] <=[(sigma t ts' ts)]=>
   ;do[(trace-vars 'foo (v vs t ts' ts))]
   [elem v t] [idem comma] [s vs ts'])
 )))

;; Typed JSON, assume lists are homogeneous
(defn tjson-value (pcg <=> json-value
 (json-symbol extend: extend ([_ x 'Str] <=> [strings x]))
 (json-number ([_ x 'Num] <=> [number x]))
 (json-value ([_ 'null 'Unit] <=> null)
  ([_ x 'Bool] <=> [json-bool x])
  ([_ x t] <=> ([json-symbol x t] / [json-number x t]))
  ([_ x t] <=> ([json-object x t] / [json-array x t]))
 )
 (json-key extend: extend ([_ x t] <=> ε [json-symbol x t]))
 (json-pair ([_ `(,n . ,v) `(Pair ,tn ,tv)] <=> [json-key n tn] |:| [json-value v tv]))
 (json-value-list ([_ '() `(List ,t)] <=> ε) ; a list of some type [[t]]
  ;([_ l `(List ,ts)] <=> [(jason-non-empty-list '|,| [_ json-value t]) l ts])
  ([_ l `(List ,ts)] <=> [(tjason-non-empty-list '|,| json-value) l ts])
  )
 (json-pair-list ([_ '() `(PList (,t1 ,t2))] <=> ε) ; a list of pairs
  ;([_ '() `(List (Pair ,t1 ,t2))] <=> ε) ; a list of pairs
  ;([_ l `(List (Pair ,t1 ,t2))] <=> [(jason-non-empty-list '|,| [_ json-pair `(Pair ,t1 ,t2)]) l])
  ([_ l `(PList . ,ts)] <=> [(tjason-non-empty-list '|,| json-pair) l ts]))
 (json-array ; promote List to an Array
  ([_ `(arr . ,es) `(Array ,t)] <=> |[| [json-value-list es `(List ,t)] |]|))
 (json-object ; promote List to an Object
  ;([_ `(obj . ,es) `(Object ,t1 ,t2)] <=> |{| [json-pair-list es `(List (Pair ,t1 ,t2))] |}|)
  ([_ `(obj . ,es) `(Object ,ts)] <=> |{| [json-pair-list es `(PList . ,ts)] |}|))
))

(def [tjson-ext-sym] (let ([extend' (extend)])
  (fn-with [apply extend'] || 'json-symbol =>
     (pcg ([_ x 'Sym] <=> [symbol x]))
  )))

(def [tjson-ext-key] (let ([extend' (extend)])
  (fn-with [apply extend'] || 'json-key =>
     (pcg ([_ x 'Num] <=> [number x])
	  ([_ x 'Bool] <=> [json-bool x]))
  )))

(def [tjson-tests] 
   (verify tjson-value1 (run* (q) (fresh (x t) (tjson-value
      '#h: true  '() x t) (== q `(,t ,x)))) ===> (Bool true))
   (verify tjson-value2.0 (run* (q) (fresh (x t) ([tjason-non-empty-list '|,| tjson-value]
      '#h: 1  '() x t) (== q `(,t ,x)))) ===> (Num (1)))
   (verify tjson-value2.1 (run* (q) (fresh (x t) ([tjason-non-empty-list '|,| tjson-value]
      '#h: 1,2  '() x t) (== q `(,t ,x)))) ===> (Num (1 2)))
   (verify tjson-value2 (run* (q) (fresh (x t) (tjson-value
      '#h:[1,2,3.1]  '() x t) (== q `(,t ,x)))) ===> ((Array Num) (arr 1 2 3.1)))
   (verify tjson-value2.1 (run 1 (q) (fresh (x t) (tjson-value
      '#h: true  '() x `(Union Num Bool)) (== q x))) =>)
   (verify tjson-value2.2 (run 1 (q) (fresh (x t) (tjson-value
      '#h:[1,2,true,3.1,false]  '() x t) (== q `(,t ,x)))) ===> ((Array (Union Num Bool)) (arr 1 2 true 3.1 false)))
   (verify tjson-value2.3 (run 1 (q) (fresh (x t) (tjson-value
      '#h:[1,2,true,3.1,"false"]  '() x t) (== q `(,t ,x)))) ===> ((Array (Union Bool Num Str)) (arr 1 2 true 3.1 "false")))
   (verify tjson-value2.c (run* (q) (fresh (x) (tjson-value
      '#h:[1,2,3.1]  '() q '(Array Num)))) ===> (arr 1 2 3.1))
   (verify tjson-value3.c (run* (q) (tjson-value
      '#h:[1,2,3.1,"a"]  '() q `(Array (Union Num Str)))) ===> (arr 1 2 3.1 "a"))
   (verify tjson-value4.c (run* (q) (fresh (y) (tjson-value
      '#h:[1,2,3.1,"a"]  '() y `(Array (Union Num ,q))))) ===> Str)
   (verify tjson-value5.c (run* (q) (fresh (y) (tjson-value
      '#h:[1,2,true,3.1,"a"]  '() y `(Array (Union Bool . ,q))))) ---> (Str Num) (Num Str))
   (verify tjson-value3 (run* (q) (fresh (x t) (tjson-value
      '#h:{"2":3.1 , "1":1e2,"0":42}  '() x t) (== q `(,t ,x))
   )) ===> ((Object (Pair Str Num)) (obj ("2" . 3.1) ("1" . 100.0) ("0" . 42))))
   (verify tjson-value4 (run* (q) (fresh (x t) (tjson-value
      '#h:{"2":[3,1] , "1":[1e2],"0":[]}  '() x t) (== q `(,t ,x))
   )) ===> ((Object (Pair Str (Array Num))) (obj ("2" . (arr 3 1)) ("1" . (arr 100.0)) ("0". (arr)))))

   (verify tjson-array1.rev (run* (q) (fresh (x y) (tjson-value
      x '() '[arr true false] `(Array Bool)) (== q x))) ===> (|[| true |,| false |]|))
   (verify tjson-object1.rev (run* (q) (fresh (x y) (tjson-value
      x '() '[obj ("a" . "b")] `(Object (Pair Str Str))) (== q x))) ===> (|{| "a" |:| "b" |}|))
   
   (verify tjson-array (run 5 (q) (fresh (x y) (tjson-value
      x '() y `(Array Bool)) (== q y))) --->
      (arr) (arr true) (arr false) (arr true true) (arr false true))
   (verify tjson-object1.enum (run* (q) (fresh (x y) (tjson-value
      x '() y `(Object (Pair Bool Num))) (== q y))) =>)
   (verify tjson-object1.enum (run 5 (q) (fresh (x y) (tjson-value
      x '() y `(Object (Pair Str Num))) (== q y))) --->
      ((obj (_.0 . _.1)) (num _.1) (str _.0))
      ((obj (_.0 . _.1) (_.2 . _.3)) (num _.1 _.3) (str _.0 _.2))
      ((obj (_.0 . _.1) (_.2 . _.3) (_.4 . _.5)) (num _.1 _.3 _.5) (str _.0 _.2 _.4))
      ((obj (_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7)) (num _.1 _.3 _.5 _.7) (str _.0 _.2 _.4 _.6))
      ((obj (_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (_.6 . _.7) (_.8 . _.9)) (num _.1 _.3 _.5 _.7 _.9) (str _.0 _.2 _.4 _.6 _.8))
      )
   (verify tjson-object1.enum (run 2 (q) (fresh (x y) (tjson-value
      x '() y `(Object (Pair Str Num))) (== q `(syntax: ,x semantics: ,y)))) --->
      ((:syntax (|{| _.0 |:| _.1 |}|) :semantics (obj (_.0 . _.1))) (num _.1) (str _.0))
      ((:syntax (|{| _.0 |:| _.1 |,| _.2 |:| _.3 |}|) :semantics (obj (_.0 . _.1) (_.2 . _.3))) (num _.1 _.3) (str _.0 _.2)))

   #;(run 4 (q) (fresh (x y) (tjson-value
      x '() y `(Array Str)) (== q `(syntax: ,x semantics: ,y))))
   
   (parameterize ([extend (tjson-ext-sym)])
    (verify tjson-value5 (run 1 (q) (fresh (x t) (tjson-value
      '#h: [{foo:quux},{bar:snarf},1]  '() x t) (== q `(,t ,x))
      )) ===> ((Array (Union (Object (Pair Sym Sym)) Num)) (arr (obj (foo . quux)) (obj (bar . snarf)) 1)))
    (verify tjson-value1.ext.rev (run* (q) (fresh (x y) (tjson-value
       x '() '[obj (a . (arr "b" "2.3"))] `(Object (Pair Sym (Array Str)))
       ) (== q x))) ===> (|{| a |:| |[| "b" |,| "2.3" |]| |}|)
      ))
   (parameterize ([extend (tjson-ext-key)])
    (verify tjson-value6 (run* (q) (fresh (x t) (tjson-value
      '#h: [{12:"quux"},{42:"snarf"}]  '() x t) (== q `(,t ,x))
      )) ===> ((Array (Object (Pair Num Str))) (arr (obj (12 . "quux")) (obj (42 . "snarf"))))
    ))
   ;[extend tjson-ext-sym]
   ;[extend (tjson-ext-key)]
   (parameterize ([extend (tjson-ext-sym)])
   (parameterize ([extend (tjson-ext-key)])
   (verify tjson-value6 (run* (q) (fresh (x t) (tjson-value
      '#h: [{12:quux},{42:snarf}]  '() x t) (== q `(,t ,x))
      )) ===> ((Array (Object (Pair Num Sym))) (arr (obj (12 . quux)) (obj (42 . snarf))))
    )
   ))
)

(def [main argv]
     (display "hello Json")(newline)
     [ne-list-tests]
     [json-tests]
     [jason-tests]
     ;[bench-tests]
     [inserto-tests]
     [tjson-tests]
 )

(cond-expand [bigloo-eval (main '())](else))
