#lang racket
(require redex)
(require "syntax.rkt")
(provide coreLang define-coreStep define-coreTest)

(define-extended-language coreLang syntax
  ; State:
  ; AST -- current state of program tree;
  ; θ   -- auxiliary state.
  [θ any]
  [auxξ θ]
  [ξ (AST auxξ)])

; ST stands for `state transformer`.
(define-syntax-rule (define-coreStep defaultState spwST joinST isReadQueueEqualTo)
  (begin

  (reduction-relation
   coreLang #:domain ξ

   (--> ((in-hole E (in-hole EU (choice number_1 number_2))) auxξ)
        ((in-hole E (in-hole EU         number_1          )) auxξ)
        "num-choice-left")

   (--> ((in-hole E (in-hole EU (choice number_1 number_2))) auxξ)
        ((in-hole E (in-hole EU                  number_2 )) auxξ)
        "num-choice-right")
  
   (--> ((in-hole E (in-hole EU       (op number_1 number_2)))  auxξ)
        ((in-hole E (in-hole EU (calc (op number_1 number_2)))) auxξ)
        "num-expr-calc"
        (side-condition
         (not (equal? (term op) (term choice)))))

   (--> ((in-hole E (in-hole EU           (projOp (μ_1 μ_2))))  auxξ)
        ((in-hole E (in-hole EU (projCalc (projOp (μ_1 μ_2))))) auxξ)
        "proj-calc")
   
   (--> ((in-hole E ((ret μ-subst) >>= (λ vName AST))) auxξ)
        ((in-hole E (subst vName μ-subst AST))         auxξ)
        ">>=-subst")

   (--> ((in-hole E (                            repeat AST))    auxξ)
        ((in-hole E (AST >>= (λ x (if x (ret x) (repeat AST))))) auxξ)
        "repeat-unroll")

   (--> ((in-hole E (                            repeatFuel number     AST))    auxξ)
        ((in-hole E (AST >>= (λ x (if x (ret x) (repeatFuel number_new AST))))) auxξ)
        "repeatFuel-unroll"
        (where number_new ,(- (term number) 1))
        (side-condition
         (> (term number) 0)))

   (--> ((in-hole E (repeatFuel 0 AST)) auxξ)
        (nofuel defaultState)
        "repeatFuel-nofuel")

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck"
        (side-condition
         (not (term (casMO=>? SM FM)))))
   
   (--> ((in-hole E (if 0 AST_1 AST_2)) auxξ)
        ((in-hole E AST_2             ) auxξ)
        "if-false")
   (--> ((in-hole E (if number AST_1 AST_2)) auxξ)
        ((in-hole E AST_1                  ) auxξ)
        "if-true"
        (side-condition
          (not (equal? (term number) 0))))

   (--> ((in-hole E (par (ret μ-value_1) (ret μ-value_2)))              auxξ)
        ((in-hole E (ret (    μ-value_1       μ-value_2))) (joinST path auxξ))
        "join"
        (where path (pathE E))
        (side-condition (term (isReadQueueEqualTo (par () ()) path auxξ))))

   (--> ((in-hole E (spw AST_1 AST_2))             auxξ)
        ((in-hole E (par AST_1 AST_2)) (spwST path auxξ))
        "spw"
        (where path (pathE E))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
      
   ; For test results brevity only.
   (--> ((ret μ) auxξ)
        ((ret μ) defaultState)
        "heap-info-erasure"
        (side-condition     ; To eliminate cycle.
         (not (equal? (term auxξ) (term defaultState)))))
   )))

(define-term defaultState ())
(define-metafunction coreLang
  spwST : path θ -> θ
  [(spwST path θ) (par θ θ)])
(define-metafunction coreLang
  joinST : path θ -> θ
  [(joinST path (par θ θ)) θ])

;;;;;;;;;;;;;;;;;
; Tests macros
;;;;;;;;;;;;;;;;;

(define testTerm-1
  (term ((spw (ret (+ 1 2)) (ret (+ 3 9))) >>= (λ v
          (ret v)))))

(define-syntax-rule (define-coreTest step defaultState)
  (begin
(test-->> step
          (term (,testTerm-1 defaultState))
          (term ((ret (3 12)) defaultState)))
))

;;;;;;;;;;;;;;;;;
; Tests execution
;;;;;;;;;;;;;;;;;

(define step (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t))
(define test (define-coreTest step defaultState))