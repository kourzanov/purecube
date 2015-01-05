;
(module Parse-c
   (library bkanren slib srfi1)
   (import (helpers "helpers.scm")
	   (loprog "loprog.sch")
	   (Parse "Parse.scm")
	   (ascript "cases.scm"))
   (export ne-la-list-of ne-la-seq-of ne-ra-list-of ne-ra-seq-of
	   expression declaration statement
	   register-enum)
   (eval (export-all))
   )

; left-recursive must be defined this way
(defn [ne-la-list-of elem comma] (pcg <=> s
 (s ([_ `(,v . ,vs)] <=> [s vs] [idem comma] [elem v])
    ([_ `(,v)] <=> [elem v])
 )))

; left-recursive must be defined this way
(defn [ne-la-seq-of elem] (pcg <=> s
 (s ([_ `(,v . ,vs)] <=> [s vs] [elem v])
    ([_ `(,v)] <=> [elem v])
 )))

(defn [ne-ra-list-of elem comma] (pcg <=> s
 (s ([_ `(,v . ,vs)] <=> [elem v] [idem comma] [s vs])
    ([_ `(,v)] <=> [elem v])
 )))

(defn [ne-ra-seq-of elem] (pcg <=> s
 (s ([_ `(,v . ,vs)] <=> [elem v] [s vs])
    ([_ `(,v)] <=> [elem v])
 )))

(def-syntax extend! extend)
(defn *def-id-constr* '(+ - __func__))
(defn id-constr! [make-parameter *def-id-constr*])
(defn (register-enum sym)
  (extend! (let ([extend' (extend!)])
	   (fn-with [apply extend']
	    || 'enumeration_constant =>
	       ;(pcg ([_ `(cnst ,s)] <=> when([idem sym]) [idem s]))
	       (pcg ([_] <=> [idem sym]))
	       ;[idem sym]
	   )))
  (id-constr! (cons sym [id-constr!]))
)

(defn (identifier Lin Lout x)
  (all 
   (symbolo x)
   (absento x [id-constr!])
   (conso x Lout Lin)
   ))

(pcg String ([_ x] <=> (strings x))
   ([_] <=> '__func__)
   )
; ; ; ; unary_operator
; ; ; ; 	: '&'
; ; ; ; 	| '*'
; ; ; ; 	| '+'
; ; ; ; 	| '-'
; ; ; ; 	| '~'
; ; ; ; 	| '!'
; ; ; ; 	;
(pcg unary_operator ([|.|] <=> ('& / '* / '+ / '- / '~ / '!)))

; ; ; ; assignment_operator
; ; ; ; 	: '='
; ; ; ; 	| MUL_ASSIGN
; ; ; ; 	| DIV_ASSIGN
; ; ; ; 	| MOD_ASSIGN
; ; ; ; 	| ADD_ASSIGN
; ; ; ; 	| SUB_ASSIGN
; ; ; ; 	| LEFT_ASSIGN
; ; ; ; 	| RIGHT_ASSIGN
; ; ; ; 	| AND_ASSIGN
; ; ; ; 	| XOR_ASSIGN
; ; ; ; 	| OR_ASSIGN
; ; ; ; 	;
(pcg assignment_operator ([_] <=> ('= / '*= / '/= / '%= / '+= / '-= / '<<= / '>>= / '&= / '^= / "|=")))


; XXX TODO: shortcut for now
(pcg type_name ([_] <=> ('int / 'long / 'short / 'float / 'double / 'char)))

;(defn c-expr (pcg <=> expression
(pcg
; ; ; ; enumeration_constant		/* before it has been defined as such */
; ; ; ; 	: IDENTIFIER
; ; ; ; 	;
  (enumeration_constant extend: extend!)
; ; ; ; primary_expression
; ; ; ; 	: IDENTIFIER
; ; ; ; 	| constant
; ; ; ; 	| string
; ; ; ; 	| '(' expression ')'
; ; ; : 	| generic_selection
; ; ; ; 	;
  ;(identifier ([_ x] <=[(=/= x '+)]=> [symbol x]))
  (primary_expression
     ([_ x] <=> [identifier x])
     ([_ x] <=> [number x])
     ([_ `(cnst ,x)] <=> [enumeration_constant x])
     ([_ x] <=> [String x])
     ([_ `(let () ,x)] <=> |(| [expression x] |)|)
     ([_ x] <=> [generic_selection x])
     )
; ; ; ; generic_selection
; ; ; ; 	: GENERIC '(' assignment_expression ',' generic_assoc_list ')'
; ; ; ; 	;
  (generic_selection
    ([_ `(genric ,ex ,al)] <=> '_Generic |(| [assignment_expression ex] |,| [generic_assoc_list al] |)|)
    )
; ; ; ; generic_association
; ; ; ; 	: type_name ':' assignment_expression
; ; ; ; 	| DEFAULT ':' assignment_expression
; ; ; ; 	;
  (generic_association
    ([_ `(ga ,tn ,ex)] <=> [type_name tn] ': [assignment_expression ex])
    ([_ `(ga default ,ex)] <=> 'default ': [assignment_expression ex])
    )
; ; ; ; generic_assoc_list
; ; ; ; 	: generic_association
; ; ; ; 	| generic_assoc_list ',' generic_association
; ; ; ; 	;
  (generic_assoc_list = (ne-la-list-of generic_association '|,|))
; ; ; ; postfix_expression
; ; ; ; : primary_expression
; ; ; ; | postfix_expression '[' expression ']'
; ; ; ; | postfix_expression '(' ')'
; ; ; ; | postfix_expression '(' argument_expression_list ')'
; ; ; ; | postfix_expression '.' IDENTIFIER
; ; ; ; | postfix_expression PTR_OP IDENTIFIER
; ; ; ; | postfix_expression INC_OP
; ; ; ; | postfix_expression DEC_OP
; ; ; : | '(' type_name ')' '{' initializer_list '}'
; ; ; : | '(' type_name ')' '{' initializer_list ',' '}'
; ; ; ; ;
  (postfix_expression1 
     ([_ `(vector-ref ,x ,y)] <=> [postfix_expression x] |[| [expression y] |]|)
     ([_ `(struct-ref ,x ,y)] <=> [postfix_expression x] |.| [identifier y])
     ([_ `(struct-deref ,x ,y)] <=> [postfix_expression x] '-> [identifier y])
     ([_ `(pre-add1 ,x)] <=> [postfix_expression x] '++)
     ([_ `(pre-sub1 ,x)] <=> [postfix_expression x] '--)
     ;([_ `(typed-init ,t ,il)] <=> |(| [type_name t] |)| |{| [initializer_list il] |}|)
     ;([_ `(typed-init ,t ,il)] <=> |(| [type_name t] |)| |{| [initializer_list il] |,| |}|)
     )
  (postfix_expression2
     ([_ `(force ,x)] <=> [postfix_expression x] |(| |)|)
     ; there is ambiguity with [[expression]], (invoke a (E 1) (E 2))==(invoke a (E 1 2))
     ; which is resolved by making (ne-list-of assignment_expression) rather than
     ; (ne-list-of expression)
     ([_ `(invoke ,x . ,args)] <=> ;[(cdrᵒ args '())]=>
	[postfix_expression x] |(| [argument_expression_list args] |)|)
     )
  (postfix_expression
    ([_ x] <=> ε([postfix_expression1 x] / [postfix_expression2 x] / [primary_expression x]))
    )
; ; ; ; unary_expression
; ; ; ; 	: postfix_expression
; ; ; ; 	| INC_OP unary_expression
; ; ; ; 	| DEC_OP unary_expression
; ; ; ; 	| unary_operator cast_expression
; ; ; ; 	| SIZEOF unary_expression
; ; ; ; 	| SIZEOF '(' type_name ')'
; ; ; ; 	| ALIGNOF '(' type_name ')'  
  (unary_expression
     ([_ `(post-add1 ,x)] <=> '++ [unary_expression x])
     ([_ `(post-sub1 ,x)] <=> '-- [unary_expression x])
     ([_ `(cast-op ,o ,c)] <=> [unary_operator o] [cast_expression c])
     ([_ x] <=> [postfix_expression x])
     ([_ `(sizeof ,t)] <=> 'sizeof |(| [type_name t] |)|)
     ([_ `(alignof ,t)] <=> 'alignof |(| [type_name t] |)|)
     )
; ; ; ; cast_expression
; ; ; ; 	: unary_expression
; ; ; ; 	| '(' type_name ')' cast_expression
	  
  (cast_expression
     ([_ `(cast ,x ,y)] <=> |(| [type_name x] |)| [cast_expression y])
     ([_ x] <=> [unary_expression x])
     )
; ; ; ; multiplicative_expression
; ; ; ; 	: cast_expression
; ; ; ; 	| multiplicative_expression '*' cast_expression
; ; ; ; 	| multiplicative_expression '/' cast_expression
; ; ; ; 	| multiplicative_expression '%' cast_expression  
  (multiplicative_expression
     ([_ `(* ,x ,y)] <=> [multiplicative_expression x] '* [cast_expression y])
     ([_ `(/ ,x ,y)] <=> [multiplicative_expression x] '/ [cast_expression y])
     ([_ `(modulo ,x ,y)] <=> [multiplicative_expression x] '% [cast_expression y])
     ([_ x] <=> [cast_expression x])
     )
; ; ; ; additive_expression
; ; ; ; 	: multiplicative_expression
; ; ; ; 	| additive_expression '+' multiplicative_expression
; ; ; ; 	| additive_expression '-' multiplicative_expression  
  (additive_expression
     ([_ `(+ ,x ,y)] <=> [additive_expression x] '+ [multiplicative_expression y])
     ([_ `(- ,x ,y)] <=> [additive_expression x] '- [multiplicative_expression y])
     ([_ x] <=> [multiplicative_expression x])
     )
; ; ; ; shift_expression
; ; ; ; 	: additive_expression
; ; ; ; 	| shift_expression LEFT_OP additive_expression
; ; ; ; 	| shift_expression RIGHT_OP additive_expression
; ; ; ; 	;
  (shift_expression
     ([_ `(bit-lsh ,x ,y)] <=> [shift_expression x] '<< [additive_expression y])
     ([_ `(bit-rsh ,x ,y)] <=> [shift_expression x] '>> [additive_expression y])
     ([_ x] <=> [additive_expression x])
     )
; ; ; ; relational_expression
; ; ; ; 	: shift_expression
; ; ; ; 	| relational_expression '<' shift_expression
; ; ; ; 	| relational_expression '>' shift_expression
; ; ; ; 	| relational_expression LE_OP shift_expression
; ; ; ; 	| relational_expression GE_OP shift_expression
; ; ; ; 	;
  (relational_expression
     ([_ `(< ,x ,y)] <=> [relational_expression x] '< [shift_expression y])
     ([_ `(> ,x ,y)] <=> [relational_expression x] '> [shift_expression y])
     ([_ `(<= ,x ,y)] <=> [relational_expression x] '<= [shift_expression y])
     ([_ `(>= ,x ,y)] <=> [relational_expression x] '>= [shift_expression y])
     ([_ x] <=> [shift_expression x])
     )
; ; ; ; equality_expression
; ; ; ; 	: relational_expression
; ; ; ; 	| equality_expression EQ_OP relational_expression
; ; ; ; 	| equality_expression NE_OP relational_expression
; ; ; ; 	;
   (equality_expression
     ([_ `(= ,x ,y)] <=> [equality_expression x] '== [relational_expression y])
     ([_ `(not (= ,x ,y))] <=> [equality_expression x] '!= [relational_expression y])
     ([_ x] <=> [relational_expression x])
     )
; ; ; ; and_expression
; ; ; ; 	: equality_expression
; ; ; ; 	| and_expression '&' equality_expression
; ; ; ; 	;
  (and_expression
     ([_ `(bit-and ,x ,y)] <=> [and_expression x] '& [equality_expression y])
     ([_ x] <=> [equality_expression x])
     ) 
; ; ; ; exclusive_or_expression
; ; ; ; 	: and_expression
; ; ; ; 	| exclusive_or_expression '^' and_expression
; ; ; ; 	;
  (xor_expression
     ([_ `(bit-xor ,x ,y)] <=> [xor_expression x] '^ [and_expression y])
     ([_ x] <=> [and_expression x])
     ) 
; ; ; ; inclusive_or_expression
; ; ; ; 	: exclusive_or_expression
; ; ; ; 	| inclusive_or_expression '|' exclusive_or_expression
; ; ; ; 	;
  (or_expression
     ([_ `(bit-or ,x ,y)] <=> [or_expression x] #\| [xor_expression y])
     ([_ x] <=> [xor_expression x])
     ) 
; ; ; ; logical_and_expression
; ; ; ; 	: inclusive_or_expression
; ; ; ; 	| logical_and_expression AND_OP inclusive_or_expression
; ; ; ; 	;
  (land_expression
     ([_ `(and ,x ,y)] <=> [land_expression x] "&&" [or_expression y])
     ([_ x] <=> [or_expression x])
     ) 
; ; ; ; logical_or_expression
; ; ; ; 	: logical_and_expression
; ; ; ; 	| logical_or_expression OR_OP logical_and_expression
; ; ; ; 	;
  (lor_expression
     ([_ `(or ,x ,y)] <=> [lor_expression x] "||" [land_expression y])
     ([_ x] <=> [land_expression x])
     ) 
; ; ; ; conditional_expression
; ; ; ; 	: logical_or_expression
; ; ; ; 	| logical_or_expression '?' expression ':' conditional_expression
; ; ; ; 	;
  (conditional_expression
     ([_ `(if ,x ,y ,z)] <=> [lor_expression x] '? [expression y] ': [conditional_expression z])
     ([_ x] <=> [lor_expression x])
     ) 
; ; ; ; assignment_expression
; ; ; ; 	: conditional_expression
; ; ; ; 	| unary_expression assignment_operator assignment_expression
; ; ; ; 	;
  (update1_expression
     ([_ `(set! ,x ,y)] <=> [unary_expression x] '= [assignment_expression y])
     ([_ `(set! ,x (* ,x ,y))] <=> [unary_expression x] '*= [assignment_expression y])
     ([_ `(set! ,x (/ ,x ,y))] <=> [unary_expression x] '/= [assignment_expression y])
     ([_ `(set! ,x (modulo ,x ,y))] <=> [unary_expression x] '%= [assignment_expression y])
     ([_ `(set! ,x (+ ,x ,y))] <=> [unary_expression x] '+= [assignment_expression y])
     ([_ `(set! ,x (- ,x ,y))] <=> [unary_expression x] '-= [assignment_expression y])
     )
  (update2_expression
     ([_ `(set! ,x (bit-lsh ,x ,y))] <=> [unary_expression x] '<<= [assignment_expression y])
     ([_ `(set! ,x (bit-rsh ,x ,y))] <=> [unary_expression x] '>>= [assignment_expression y])
     ([_ `(set! ,x (bit-and ,x ,y))] <=> [unary_expression x] '&= [assignment_expression y])
     ([_ `(set! ,x (bit-xor ,x ,y))] <=> [unary_expression x] '^= [assignment_expression y])
     ([_ `(set! ,x (bit-or ,x ,y))] <=> [unary_expression x] "|=" [assignment_expression y])
     )
  (assignment_expression
     ;generic rule
     ;([_ `(update ,x ,o ,y)] <=> [unary_expression x] [assignment_operator o] [assignment_expression y])
     ([_ x] <=> ε([update1_expression x] / [update2_expression x] / [conditional_expression x]))
     )
  ; ; ; ; argument_expression_list
; ; ; ; 	: assignment_expression
; ; ; ; 	| argument_expression_list ',' assignment_expression
; ; ; ; 	;
  (argument_expression_list = (ne-la-list-of assignment_expression '|,|))
; ; ; ; expression
; ; ; ; 	: assignment_expression
; ; ; ; 	| expression ',' assignment_expression
  (expression ([_ `(E . ,x)] <=> [(ne-la-list-of assignment_expression '|,|) x]))
; ; ; ; constant_expression
; ; ; ; 	: conditional_expression	/* with constraints */
; TODO; 	;
;;WHAT CONSTRAINTS?
  (constant_expression = conditional_expression)
)

;(defn c-decl (pcg <=> declaration
(pcg
; ; ; ; static_assert_declaration
; ; ; ; 	: STATIC_ASSERT '(' constant_expression ',' STRING_LITERAL ')' ';'
; ; ; ; 	;
  (static_assert_declaration
     ([_ `(assert ,e ,s)] <=> '_Static_assert |(| [constant_expression e] |,| [strings s] |)| #\;)
     )   
; ; ; ; declaration
; ; ; ; 	: declaration_specifiers ';'
; ; ; ; 	| declaration_specifiers init_declarator_list ';'
; ; ; ; 	| static_assert_declaration
; ; ; ; 	;
  (declaration
     ([_ `(decls ,ss)] <=> [declaration_specifiers ss] #\;)
     ([_ `(decls-init ,ss ,ini)] <=> [declaration_specifiers ss] [init_declarator_list ini] #\;)
     ([_ sa] <=> [static_assert_declaration sa])
     )
; ; ; ; declaration_specifiers
; ; ; ; 	: storage_class_specifier declaration_specifiers
; ; ; ; 	| storage_class_specifier
; ; ; ; 	| type_specifier declaration_specifiers
; ; ; ; 	| type_specifier
; ; ; ; 	| type_qualifier declaration_specifiers
; ; ; ; 	| type_qualifier
; ; ; ; 	| function_specifier declaration_specifiers
; ; ; ; 	| function_specifier
; ; ; ; 	| alignment_specifier declaration_specifiers
; ; ; ; 	| alignment_specifier
; ; ; ; 	;
  ;; this is way too slow with alexpander
  ; (declaration_specifiers'
  ;    ([_ `(decl ,sc . ,ds)] <=> [storage_class_specifier sc] [declaration_specifiers ds])
  ;    ([_ `(decl ,sc)] <=> [storage_class_specifier sc])
  ;    ([_ `(decl ,ts . ,ds)] <=> [type_specifier ts] [declaration_specifiers ds])
  ;    ([_ `(decl ,ts)] <=> [type_specifier ts])
  ;    ([_ `(decl ,ts . ,ds)] <=> [type_qualifier ts] [declaration_specifiers ds])
  ;    ([_ `(decl ,ts)] <=> [type_qualifier ts])
  ;    ([_ `(decl ,sc . ,ds)] <=> [function_specifier sc] [declaration_specifiers ds])
  ;    ([_ `(decl ,sc)] <=> [function_specifier sc])
  ;    ([_ `(decl ,sc . ,ds)] <=> [alignment_specifier sc] [declaration_specifiers ds])
  ;    ([_ `(decl ,sc)] <=> [alignment_specifier sc])
  ;    )
  ; alternative to the above
  (declarations
     ([_ x] <=> ε([storage_class_specifier x] / [type_specifier x] / [type_qualifier x] /
		  [function_specifier x] / [alignment_specifier x ]))
     )
  (declaration_specifiers
     ([_ `(decls . ,ds)] <=> [(ne-ra-seq-of declarations) ds])
     )
; ; ; ; init_declarator
; ; ; ; 	: declarator '=' initializer
; ; ; ; 	| declarator
; ; ; ; 	;
  (init_declarator
     ([_ `(init ,d ,i)] <=> [declarator d] '= [initializer i])
     ([_ `(init ,d)] <=> [declarator d])
     )
; ; ; ; init_declarator_list
; ; ; ; 	: init_declarator
; ; ; ; 	| init_declarator_list ',' init_declarator
; ; ; ; 	;
  (init_declarator_list = (ne-la-list-of init_declarator '|,|))
; ; ; ; storage_class_specifier
; ; ; ; 	: TYPEDEF	/* identifiers must be flagged as TYPEDEF_NAME */
; ; ; ; 	| EXTERN
; ; ; ; 	| STATIC
; ; ; ; 	| THREAD_LOCAL
; ; ; ; 	| AUTO
; ; ; ; 	| REGISTER
; ; ; ; 	;
  (storage_class_specifier
     ([_] <=> ('typedef / 'extern / 'static / '_Thread_local / 'auto / 'register))
     )
; ; ; ; type_specifier
; ; ; ; 	: VOID
; ; ; ; 	| CHAR
; ; ; ; 	| SHORT
; ; ; ; 	| INT
; ; ; ; 	| LONG
; ; ; ; 	| FLOAT
; ; ; ; 	| DOUBLE
; ; ; ; 	| SIGNED
; ; ; ; 	| UNSIGNED
; ; ; ; 	| BOOL
; ; ; ; 	| COMPLEX
; ; ; ; 	| IMAGINARY	  	/* non-mandated extension */
; ; ; ; 	| atomic_type_specifier
; ; ; ; 	| struct_or_union_specifier
; ; ; ; 	| enum_specifier
; ; ; ; 	| TYPEDEF_NAME		/* after it has been defined as such */
; ; ; ; 	;
  (typedef_name extend: extend!)
  (type_specifier
     ([_] <=> ('void / 'char / 'short / 'int / 'long / 'float / 'double / 'signed / 'unsigned / '_Bool / '_Complex / '_Imaginary))
     ([_ x] <=> [atomic_type_specifier x])
     ([_ x] <=> [struct_or_union_specifier x])
     ([_ x] <=> [enum_specifier x])
     ([_ x] <=> [typedef_name x])
     )
; ; ; ; struct_or_union_specifier
; ; ; ; 	: struct_or_union '{' struct_declaration_list '}'
; ; ; ; 	| struct_or_union IDENTIFIER '{' struct_declaration_list '}'
; ; ; ; 	| struct_or_union IDENTIFIER
; ; ; ; 	;
  (struct_or_union_specifier
     ([_ `(,st . ,dl)] <=> [struct_or_union st] |{| [struct_declaration_list dl] |}|) 
     ([_ `(,st ,id . ,dl)] <=> [struct_or_union st] [identifier id] |{| [struct_declaration_list dl] |}|)
     ([_ `(,st ,id)] <=> [struct_or_union st] [identifier id])
     )
; ; ; ; struct_or_union
; ; ; ; 	: STRUCT
; ; ; ; 	| UNION
; ; ; ; 	;
  (struct_or_union
     ([_] <=> ('struct / 'union))
     )
; ; ; ; struct_declaration
; ; ; ; 	: specifier_qualifier_list ';'	/* for anonymous struct/union */
; ; ; ; 	| specifier_qualifier_list struct_declarator_list ';'
; ; ; ; 	| static_assert_declaration
; ; ; ; 	;
  (struct_declaration
     ([_ `(anon ,sl)] <=> [specifier_qualifier_list sl] #\;)
     ([_ `(,sd ,sl)] <=> [specifier_qualifier_list sl] [struct_declarator_list sd] #\;)
     ([_ x] <=> [static_assert_declaration x])
     )
; ; ; ; struct_declaration_list
; ; ; ; 	: struct_declaration
; ; ; ; 	| struct_declaration_list struct_declaration
; ; ; ; 	;
  (struct_declaration_list = (ne-la-seq-of struct_declaration))
; ; ; ; specifier_qualifier_list
; ; ; ; 	: type_specifier specifier_qualifier_list
; ; ; ; 	| type_specifier
; ; ; ; 	| type_qualifier specifier_qualifier_list
; ; ; ; 	| type_qualifier
; ; ; ; 	;
  (specifier_qualifier_elem
     ([_ x] <=> ε([type_specifier x] / [type_qualifier x]))
     )
  (specifier_qualifier_list = (ne-ra-seq-of specifier_qualifier_elem))
; ; ; ; struct_declarator
; ; ; ; 	: ':' constant_expression
; ; ; ; 	| declarator ':' constant_expression
; ; ; ; 	| declarator
; ; ; ; 	;
  (struct_declarator
    ([_ `(anondecl ,e)] <=> ': [constant_expression e])
    ([_ `(strdecl ,d ,e)] <=> [declarator d] ': [constant_expression e])
    ([_ `(sdecl ,d)] <=> [declarator d])
    )
; ; ; ; struct_declarator_list
; ; ; ; 	: struct_declarator
; ; ; ; 	| struct_declarator_list ',' struct_declarator
; ; ; ; 	;
  (struct_declarator_list = (ne-la-list-of struct_declarator '|,|))

; ; ; ; enum_specifier
; ; ; ; 	: ENUM '{' enumerator_list '}'
; ; ; ; 	| ENUM '{' enumerator_list ',' '}'
; ; ; ; 	| ENUM IDENTIFIER '{' enumerator_list '}'
; ; ; ; 	| ENUM IDENTIFIER '{' enumerator_list ',' '}'
; ; ; ; 	| ENUM IDENTIFIER
; ; ; ; 	;
  (enum_specifier
    ([_ `(enum ,el)] <=> 'enum |{| [enumerator_list el] |}|)
    ([_ `(enum ,el)] <=> 'enum |{| [enumerator_list el] |,| |}|)
    ([_ `(enum ,id ,el)] <=> 'enum [identifier id] |{| [enumerator_list el] |}|)
    ([_ `(enum ,id ,el)] <=> 'enum [identifier id] |{| [enumerator_list el] |,| |}|)
    ([_ `(enum ,id ,el)] <=> 'enum [identifier id])
    )
; ; ; ; enumerator	/* identifiers must be flagged as ENUMERATION_CONSTANT */
; ; ; ; 	: enumeration_constant '=' constant_expression
; ; ; ; 	| enumeration_constant
; ; ; ; 	;
  (enumerator
    ([_ `(enum ,ec ,ce)] <=> [enumeration_constant ec] '= [constant_expression ce])
    ([_ `(enum ,ec)] <=> [enumeration_constant ec])
    )
; ; ; ; enumerator_list
; ; ; ; 	: enumerator
; ; ; ; 	| enumerator_list ',' enumerator
; ; ; ; 	;
  (enumerator_list = (ne-la-list-of enumerator '|,|))
; ; ; ; atomic_type_specifier
; ; ; ; 	: ATOMIC '(' type_name ')'
; ; ; ; 	;
  (atomic_type_specifier
     ([_ `(atomic ,t)] <=> '_Atomic |(| [type_name t] |)|)
     )
; ; ; ; type_qualifier
; ; ; ; 	: CONST
; ; ; ; 	| RESTRICT
; ; ; ; 	| VOLATILE
; ; ; ; 	| ATOMIC
; ; ; ; 	;
  (type_qualifier
    ([_] <=> ('const / 'restrict / 'volatile / '_Atomic))
    )
; ; ; ; function_specifier
; ; ; ; 	: INLINE
; ; ; ; 	| NORETURN
; ; ; ; 	;
  (function_specifier
    ([_] <=> ('inline / '_Noreturn))
    )
; ; ; ; alignment_specifier
; ; ; ; 	: ALIGNAS '(' type_name ')'
; ; ; ; 	| ALIGNAS '(' constant_expression ')'
; ; ; ; 	;
  (alignment_specifier
    ([_ `(align-as-type ,t)] <=> '_Alignas |(| [type_name t] |)|)
    ([_ `(align-as-expr ,e)] <=> '_Alignas |(| [constant_expression e] |)|)
    )
; ; ; ; declarator
; ; ; ; 	: pointer direct_declarator
; ; ; ; 	| direct_declarator
; ; ; ; 	;
  (declarator
    ([_ `(ptr ,p ,x)] <=> [pointer p] [direct_declarator x])
    ([_ x] <=> [direct_declarator x])
    )
; ; ; ; direct_declarator
; ; ; ; 	: IDENTIFIER
; ; ; ; 	| '(' declarator ')'
; ; ; ; 	| direct_declarator '[' ']'
; ; ; ; 	| direct_declarator '[' '*' ']'
; ; ; ; 	| direct_declarator '[' STATIC type_qualifier_list assignment_expression ']'
; ; ; ; 	| direct_declarator '[' STATIC assignment_expression ']'
; ; ; ; 	| direct_declarator '[' type_qualifier_list '*' ']'
; ; ; ; 	| direct_declarator '[' type_qualifier_list STATIC assignment_expression ']'
; ; ; ; 	| direct_declarator '[' type_qualifier_list assignment_expression ']'
; ; ; ; 	| direct_declarator '[' type_qualifier_list ']'
; ; ; ; 	| direct_declarator '[' assignment_expression ']'
; ; ; ; 	| direct_declarator '(' parameter_type_list ')'
; ; ; ; 	| direct_declarator '(' ')'
; ; ; ; 	| direct_declarator '(' identifier_list ')'
; ; ; ; 	;
  (direct_declarator1
    ([_ `(dd ,d)] <=> |(| [declarator d] |)|)
    ([_ `(dd-arr-static ,d ,tq ,e)] <=> [direct_declarator d] |[| 'static [type_qualifier_list tq] [assignment_expression e] |]|)
    ([_ `(dd-arr-static ,d ,e)] <=> [direct_declarator d] |[| 'static [assignment_expression e] |]|)
    ([_ `(dd-arr-static ,d ,tq ,e)] <=> [direct_declarator d] |[| [type_qualifier_list tq] 'static [assignment_expression e] |]|)
    )
  (direct_declarator2
    ([_ `(dd-arr ,d)] <=> [direct_declarator d] |[| |]|)
    ([_ `(dd-arr ,d)] <=> [direct_declarator d] |[| '* |]|)
    ([_ `(dd-arr ,d ,tq)] <=> [direct_declarator d] |[| [type_qualifier_list tq] '* |]|)
    ([_ `(dd-arr ,d ,tq ,e)] <=> [direct_declarator d] |[| [type_qualifier_list tq] [assignment_expression e] |]|)
    ([_ `(dd-arr ,d ,tq)] <=> [direct_declarator d] |[| [type_qualifier_list tq] |]|)
    ([_ `(dd-arr ,d ,e)] <=> [direct_declarator d] |[| [assignment_expression e] |]|)
    )
  (direct_declarator3
    ([_ `(dd-fun ,d ,pl)] <=> [direct_declarator d] |(| [parameter_type_list pl] |)|)
    ([_ `(dd-fun ,d)] <=> [direct_declarator d] |(| |)|)
    ([_ `(dd-fun ,d ,il)] <=> [direct_declarator d] |(| [identifier_list il] |)|)
    )
  (direct_declarator
    ([_ x] <=> ε([identifier x] / [direct_declarator1 x] / [direct_declarator2 x] / [direct_declarator3 x]))
    )
; ; ; ; pointer
; ; ; ; 	: '*' type_qualifier_list pointer
; ; ; ; 	| '*' type_qualifier_list
; ; ; ; 	| '*' pointer
; ; ; ; 	| '*'
; ; ; ; 	;
  (pointer
    ([_ `(ptr ,ql ,p)] <=> '* [type_qualifier_list ql] [pointer p])
    ([_ `(ptr ,ql)] <=> '* [type_qualifier_list ql])
    ([_ `(ptr ,ql ,p)] <=> '* [pointer p])
    ([_ `(ptr ,ql ,p)] <=> '*)
    )
; ; ; ; type_qualifier_list
; ; ; ; 	: type_qualifier
; ; ; ; 	| type_qualifier_list type_qualifier
; ; ; ; 	;
  (type_qualifier_list = (ne-la-seq-of type_qualifier))
; ; ; ; parameter_type_list
; ; ; ; 	: parameter_list ',' ELLIPSIS
; ; ; ; 	| parameter_list
; ; ; ; 	;
  (parameter_type_list
    ([_ `(var-args ,pl)] <=> [parameter_list pl] |,| ELLIPSIS)
    ([_ `(args ,pl)] <=> [parameter_list pl])
    )
; ; ; ; parameter_declaration
; ; ; ; 	: declaration_specifiers declarator
; ; ; ; 	| declaration_specifiers abstract_declarator
; ; ; ; 	| declaration_specifiers
; ; ; ; 	;
  (parameter_declaration
    ([_ `(pd ,ds ,d)] <=> [declaration_specifiers ds] [declarator d])
    ([_ `(pd ,ds ,ad)] <=> [declaration_specifiers ds] [abstract_declarator ad])
    ([_ `(pd ,ds)] <=> [declaration_specifiers ds])
    )
; ; ; ; parameter_list
; ; ; ; 	: parameter_declaration
; ; ; ; 	| parameter_list ',' parameter_declaration
; ; ; ; 	;
  (parameter_list = (ne-la-list-of parameter_declaration '|,|))
; ; ; ; identifier_list
; ; ; ; 	: IDENTIFIER
; ; ; ; 	| identifier_list ',' IDENTIFIER
; ; ; ; 	;
  (identifier_list = (ne-la-list-of identifier '|,|))
; ; ; ; type_name
; ; ; ; 	: specifier_qualifier_list abstract_declarator
; ; ; ; 	| specifier_qualifier_list
; ; ; ; 	;
  (type_name'
    ([_ `(type ,sl ,ad)] <=> [specifier_qualifier_list sl] [abstract_declarator ad])
    ([_ `(type ,sl)] <=> [specifier_qualifier_list sl])
    )
; ; ; ; abstract_declarator
; ; ; ; 	: pointer direct_abstract_declarator
; ; ; ; 	| pointer
; ; ; ; 	| direct_abstract_declarator
; ; ; ; 	;
  (abstract_declarator
    ([_ `(ad ,p ,da)] <=> [pointer p] [direct_abstract_declarator da])
    ([_ `(ad ,p)] <=> [pointer p])
    ([_ `(ad ,da)] <=>  [direct_abstract_declarator da])
    )
; ; ; ; direct_abstract_declarator
; ; ; ; 	: '(' abstract_declarator ')'
; ; ; ; 	| '[' ']'
; ; ; ; 	| '[' '*' ']'
; ; ; ; 	| '[' STATIC type_qualifier_list assignment_expression ']'
; ; ; ; 	| '[' STATIC assignment_expression ']'
; ; ; ; 	| '[' type_qualifier_list STATIC assignment_expression ']'
; ; ; ; 	| '[' type_qualifier_list assignment_expression ']'
; ; ; ; 	| '[' type_qualifier_list ']'
; ; ; ; 	| '[' assignment_expression ']'
; ; ; ; 	| direct_abstract_declarator '[' ']'
; ; ; ; 	| direct_abstract_declarator '[' '*' ']'
; ; ; ; 	| direct_abstract_declarator '[' STATIC type_qualifier_list assignment_expression ']'
; ; ; ; 	| direct_abstract_declarator '[' STATIC assignment_expression ']'
; ; ; ; 	| direct_abstract_declarator '[' type_qualifier_list assignment_expression ']'
; ; ; ; 	| direct_abstract_declarator '[' type_qualifier_list STATIC assignment_expression ']'
; ; ; ; 	| direct_abstract_declarator '[' type_qualifier_list ']'
; ; ; ; 	| direct_abstract_declarator '[' assignment_expression ']'
; ; ; ; 	| '(' ')'
; ; ; ; 	| '(' parameter_type_list ')'
; ; ; ; 	| direct_abstract_declarator '(' ')'
; ; ; ; 	| direct_abstract_declarator '(' parameter_type_list ')'
; ; ; ; 	;
  (direct_abstract_declarator1
    ([_ `(da ())] <=> |[| |]|)
    ([_ `(da ())] <=> |[| '* |]|)
    )
  (direct_abstract_declarator2
    ([_ `(da static ,tql ,ae)] <=> |[| 'static [type_qualifier_list tql] [assignment_expression ae] |]|)
    ([_ `(da static ,ae)] <=> |[| 'static [assignment_expression ae] |]|)
    ([_ `(da static ,tql ,ae)] <=> |[| [type_qualifier_list tql] 'static [assignment_expression ae] |]|)
    )
  (direct_abstract_declarator3
    ([_ `(da ,tql ,ae)] <=> |[| [type_qualifier_list tql] [assignment_expression ae] |]|)
    ([_ `(da ,tql ,ae)] <=> |[| [type_qualifier_list tql] |]|)
    ([_ `(da ,tql ,ae)] <=> |[| [assignment_expression ae] |]|)
    )
  (direct_abstract_declarator4
    ([_ `(daf ())] <=> |(| |)|)
    ([_ `(daf ,l)] <=> |(| [parameter_type_list l] |)|)
    )
  (direct_abstract_declarator_elem
    ([_ x] <=> ε([direct_abstract_declarator1 x] / [direct_abstract_declarator2 x] / [direct_abstract_declarator3 x] / [direct_abstract_declarator4 x]))
    )
  (direct_abstract_declarator_list = (ne-la-seq-of direct_abstract_declarator_elem))
  (direct_abstract_declarator
     ([_ `(da ,ad)] <=> |(| [abstract_declarator ad] |)|)
     ([_ x] <=> [direct_abstract_declarator_list x])
     )
; ; ; ; initializer
; ; ; ; 	: '{' initializer_list '}'
; ; ; ; 	| '{' initializer_list ',' '}'
; ; ; ; 	| assignment_expression
; ; ; ; 	;
  (initializer
    ([_ `(init ,il)] <=> |{| [initializer_list il] |}|)
    ([_ `(init ,il)] <=> |{| [initializer_list il] |,| |}|)
    ([_ `(init ,ae)] <=> [assignment_expression ae])
    )
; ; ; ; initializer_list
; ; ; ; 	: designation initializer
; ; ; ; 	| initializer
; ; ; ; 	| initializer_list ',' designation initializer
; ; ; ; 	| initializer_list ',' initializer
; ; ; ; 	;
  (initializer_list_elem
    ([_ `(,d . ,i)] <=> [designation d] [initializer i])
    ([_ i] <=> [initializer i])
    )
  (initializer_list = (ne-la-list-of initializer_list_elem '|,|))
; ; ; ; designation
; ; ; ; 	: designator_list '='
; ; ; ; 	;
  (designation
    ([_ dl] <=> [designator_list dl] '=)
    )
; ; ; ; designator
; ; ; ; 	: '[' constant_expression ']'
; ; ; ; 	| '.' IDENTIFIER
; ; ; ; 	;
  (designator
    ([_ `(desig ,ce)] <=> |[| [constant_expression ce] |]|)
    ([_ `(desig ,id)] <=> |.| [identifier id])
    )
; ; ; ; designator_list
; ; ; ; 	: designator
; ; ; ; 	| designator_list designator
; ; ; ; 	;
  (designator_list = (ne-la-seq-of designator))
)

;(defn c-prog (pcg <=> statement
(pcg
; ; ; ; statement
; ; ; ; 	: labeled_statement
; ; ; ; 	| compound_statement
; ; ; ; 	| expression_statement
; ; ; ; 	| selection_statement
; ; ; ; 	| iteration_statement
; ; ; ; 	| jump_statement
; ; ; ; 	;
  (statement
    ([_ x] <=> ε([labeled_statement x] / [compound_statement x] /
		 [expression_statement x] / [selection_statement x] /
		 [iteration_statement x] / [jump_statement x]))
    )
; ; ; ; labeled_statement
; ; ; ; 	: IDENTIFIER ':' statement
; ; ; ; 	| CASE constant_expression ':' statement
; ; ; ; 	| DEFAULT ':' statement
; ; ; ; 	;
  (labeled_statement
    ([_ `(lab ,id ,st)] <=> [identifier id] ': [statement st])
    ([_ `(case-lab ,ex ,st)] <=> 'case [constant_expression ex] ': [statement st])
    ([_ `(case-lab default ,st)] <=> 'default ': [statement st])
    )
; ; ; ; compound_statement
; ; ; ; 	: '{' '}'
; ; ; ; 	| '{'  block_item_list '}'
; ; ; ; 	;
  (compound_statement
    ([_ `(begin)] <=> |{| |}|)
    ([_ `(begin ,b)] <=> |{| [block_item_list b] |}|)
    )
; ; ; ; block_item
; ; ; ; 	: declaration
; ; ; ; 	| statement
; ; ; ; 	;
  (block_item
    ([_ x] <=> ε([declaration x] / [statement x]))
    )
; ; ; ; block_item_list
; ; ; ; 	: block_item
; ; ; ; 	| block_item_list block_item
; ; ; ; 	;
  (block_item_list = (ne-la-seq-of block_item))
; ; ; ; expression_statement
; ; ; ; 	: ';'
; ; ; ; 	| expression ';'
; ; ; ; 	;
  (expression_statement
    ([_ `(nop)] <=> #\;)
    ([_ `(stmt ,ex)] <=> [expression ex] #\;)
    )
; ; ; ; selection_statement
; ; ; ; 	: IF '(' expression ')' statement ELSE statement
; ; ; ; 	| IF '(' expression ')' statement
; ; ; ; 	| SWITCH '(' expression ')' statement
; ; ; ; 	;
  (selection_statement
    ([_ `(if ,ex ,s1 ,s2)] <=> 'if |(| [expression ex] |)| [statement s1] 'else [statement s2])
    ([_ `(if ,ex ,s1 #f)] <=> 'if |(| [expression ex] |)| [statement s1])
    ([_ `(case ,ex ,st)] <=> 'switch |(| [expression ex] |)| [statement st])
    )
; ; ; ; iteration_statement
; ; ; ; 	: WHILE '(' expression ')' statement
; ; ; ; 	| DO statement WHILE '(' expression ')' ';'
; ; ; ; 	| FOR '(' expression_statement expression_statement ')' statement
; ; ; ; 	| FOR '(' expression_statement expression_statement expression ')' statement
; ; ; ; 	| FOR '(' declaration expression_statement ')' statement
; ; ; ; 	| FOR '(' declaration expression_statement expression ')' statement
; ; ; ; 	;
  (iteration_statement
    ([_ `(while ,ex ,st)] <=> 'while |(| [expression ex] |)| [statement st])
    ([_ `(do ,ex ,st)] <=> 'do [statement st] 'while |(| [expression ex] |)|)
    ([_ `(for ,es1 ,es2 ,st)] <=> 'for |(| [expression_statement es1] [expression_statement es2] |)| [statement st])
    ([_ `(for ,es1 ,es2 ,ex ,st)] <=> 'for |(| [expression_statement es1] [expression_statement es2] [expression ex] |)| [statement st])
    ([_ `(for ,d ,es2 ,st)] <=> 'for |(| [declaration d] [expression_statement es2] |)| [statement st])
    ([_ `(for ,d ,es2 ,ex ,st)] <=> 'for |(| [declaration d] [expression_statement es2] [expression ex] |)| [statement st])
    )
; ; ; ; jump_statement
; ; ; ; 	: GOTO IDENTIFIER ';'
; ; ; ; 	| CONTINUE ';'
; ; ; ; 	| BREAK ';'
; ; ; ; 	| RETURN ';'
; ; ; ; 	| RETURN expression ';'
; ; ; ; 	;
  (jump_statement
    ([_ `(goto ,id)] <=> 'goto [identifier id])
    ([_ 'continue] <=> 'continue #\;)
    ([_ 'break] <=> 'break #\;)
    ([_ 'return] <=> 'return #\;)
    ([_ `(return ,ex)] <=> 'return [expression ex] #\;)
    )
; ; ; ; external_declaration
; ; ; ; 	: function_definition
; ; ; ; 	| declaration
; ; ; ; 	;
  (external_declaration
    ([_ x] <=> ε([function_definition x] / [declaration x]))
    )
; ; ; ; translation_unit
; ; ; ; 	: external_declaration
; ; ; ; 	| translation_unit external_declaration
; ; ; ; 	;
  (translation_unit = (ne-la-seq-of external_declaration))
; ; ; ; function_definition
; ; ; ; 	: declaration_specifiers declarator declaration_list compound_statement
; ; ; ; 	| declaration_specifiers declarator compound_statement
  (function_definition
    ([_ `(fun ,ds ,d ,dl ,b)] <=> [declaration_specifiers ds] [declarator d] [declaration_list dl] [compound_statement b])
    ([_ `(fun ,ds ,d ,b)] <=> [declaration_specifiers ds] [declarator d] [compound_statement b])
    )
; ; ; ; declaration_list
; ; ; ; 	: declaration
; ; ; ; 	| declaration_list declaration
; ; ; ; 	;
  (declaration_list = (ne-la-seq-of declaration))
)
