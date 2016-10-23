#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(require "coreUtils.rkt")
(provide (all-defined-out))

(define nonPostponedReadConst (term None))

(define-metafunction coreLang
  snocT : any (any ...) -> (any ...)
  [(snocT any_0 any_1) (appendT any_1 (any_0))])

(define-metafunction coreLang
  ;; incPaths : (L|R) paths -> paths
  [(incPaths any paths)
   ,(map (λ (x) (list (term any) x))
         (term paths))])

;; Returns random element from the list.
(define select-random
  (lambda (ls)
    (let ((len (length ls)))
      (list-ref ls (random len)))))

(define-metafunction coreLang
  isUsed : vName AST -> boolean
  [(isUsed vName AST) #f
                      (side-condition (equal? (term (subst vName 1 AST)) (term AST)))]
  [(isUsed vName AST) #t])

(define-metafunction coreLang
  normalize_subst : ξ -> ξ
  [(normalize_subst
     ((in-hole E ((ret μ-subst) >>= (λ vName AST))) auxξ))
   (normalize_subst
     ((in-hole E (subst vName μ-subst AST))         auxξ))
   (side-condition (not (term (isUsed vName AST))))]

  [(normalize_subst (AST auxξ)) ((normalize_expr AST) auxξ)])

(define-metafunction coreLang
  normalize_expr : AST -> AST

  [(normalize_expr (in-hole E (in-hole EU μ    )))
   (normalize_expr (in-hole E (in-hole EU μ_new)))

   (where μ_new (calcμ μ))
   (side-condition (not (equal? (term μ) (term μ_new))))]

  [(normalize_expr AST) AST])

(define-metafunction coreLang
  normalize : ξ -> ξ
  [(normalize (AST auxξ)) (normalize_subst (AST auxξ))])

(define-metafunction coreLang
  isLocationDeallocated : ι-var auxξ -> boolean
  [(isLocationDeallocated ι (any_0 ... (Deallocated listι) any_1 ...))
   ,(not (false? (member (term ι) (term listι))))]
  [(isLocationDeallocated ι-var auxξ) #f])

(define-metafunction coreLang
  deallocate : ι auxξ -> auxξ
  [(deallocate ι (any_0 ... (Deallocated listι) any_1 ...))
   (any_0 ... (Deallocated ,(cons (term ι) (term listι))) any_1 ...)])

(define-metafunction coreLang
  isLocationUninitialized : ι-var σ-dd path auxξ -> boolean
  [(isLocationUninitialized ι σ-dd path auxξ)
   ,(or (equal? (term (getLastTimestamp ι η)) (term -1))
        (equal? (term None)
                (term (lookup ι
                              (frontMerge σ-dd (getReadσ path auxξ))))))
   (where η (getη auxξ))]
  [(isLocationUninitialized vName σ-dd path auxξ) #f])

; ST stands for `state transformer`.
(define-syntax-rule (define-coreStep defaultState)
  (begin

  (reduction-relation coreLang #:domain ξ
   
   (--> (AST     auxξ)
        (AST_new auxξ)
        "calc_expr"
        (where AST_new (normalize_expr AST))
        (side-condition (not (equal? (term AST) (term AST_new)))))

   (-->  ((in-hole E (in-hole Eif ((ret μ-subst) >>= (λ vName AST)))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (subst vName μ-subst AST)))         auxξ))
        ">>=-subst")
   
   (-->  ((in-hole E (in-hole EU (in-hole EU2 (choice number_1 number_2)))) auxξ)
        (normalize
         ((in-hole E (in-hole EU (in-hole EU2         number_1          ))) auxξ))
        "num-choice-left")

   (-->  ((in-hole E (in-hole EU (in-hole EU2 (choice number_1 number_2)))) auxξ)
        (normalize
         ((in-hole E (in-hole EU (in-hole EU2                  number_2 ))) auxξ))
        "num-choice-right")
  
   (-->  ((in-hole E (                            repeat AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeat AST))))) auxξ))
        "repeat-unroll")

   (-->  ((in-hole E (                            repeatFuel number     AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeatFuel number_new AST))))) auxξ))
        "repeatFuel-unroll"
        (where number_new ,(- (term number) 1))
        (side-condition (> (term number) 0)))

   (--> ((in-hole E (repeatFuel 0 AST)) auxξ)
        (nofuel defaultState)
        "repeatFuel-nofuel")

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-uninitialized"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var () path auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-uninitialized"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var σ-dd path auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (read RM ι-var)) auxξ)
        (stuck defaultState)
        "read-stuck"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var () path auxξ))
                            (term (isLocationDeallocated   ι-var auxξ)))))

   (--> ((in-hole E (readCon RM ι-var σ-dd)) auxξ)
        (stuck defaultState)
        "readCon-stuck"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var σ-dd path auxξ))
                            (term (isLocationDeallocated   ι-var auxξ)))))

   (--> ((in-hole E (write WM ι)) auxξ)
        (stuck defaulState)
        "write-stuck" ; segfault
        (side-condition (term (isLocationDeallocated ι-var auxξ))))
  
   (-->  ((in-hole E (if 0 AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E AST_1             ) auxξ))
        "if-false")

   (-->  ((in-hole E (if number AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E AST_0                  ) auxξ))
        "if-true"
        (side-condition
          (not (equal? (term number) 0))))

   (-->  ((in-hole E (par (ret μ-value_0) (ret μ-value_1)))              auxξ)
        (normalize 
         ((in-hole E (ret (    μ-value_0       μ-value_1))) (joinST path auxξ)))
        "join"
        (where path (pathE E))
        (side-condition (term (isReadQueueEqualTo (par () ()) path auxξ))))

   (-->  ((in-hole E (spw AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E (par AST_0 AST_1)) auxξ_new))
        "spw"
        (where path (pathE E))
        (where auxξ_new (spwST path auxξ))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
     
   ; For test results brevity only.
   (--> ((ret μ-value) auxξ)
         (ret μ-value)
        "auxξ-erasure")
        ;; (side-condition     ; Not to introduce a cycle rule.
        ;;  (not (equal? (term auxξ) (term defaultState)))))
   
   (-->  AST
        (AST defaultState)
        "add-default-auxξ"
        (side-condition     ; Not to introduce a cycle with "auxξ-erasure" rule.
         (not (redex-match coreLang (ret μ-value) (term AST)))))

   (-->  ((in-hole E (dealloc ι)) auxξ)
        (normalize
         ((in-hole E (ret     0)) auxξ_new))
        "deallocate"
        (where auxξ_new (deallocate ι auxξ))
        (side-condition (not (term (isLocationDeallocated ι auxξ)))))

   (--> ((in-hole E (dealloc ι)) auxξ)
        (stuck defaultState)
        "deallocate-stuck"
        (side-condition (term (isLocationDeallocated ι auxξ))))
   )))

;;;;;;;;;;;;;;;;
; Test macros
;;;;;;;;;;;;;;;;

(define testTerm-112
  (term ((spw (ret (+ 1 2)) (ret (+ 3 9))) >>= (λ v
          (ret v)))))

#|
ret 5 < 5
|#
(define testTerm-2 (term ((ret (< 5 5)) >>= (λ x (ret x)))))


(define-syntax-rule (define-coreTest step defaultState)
  (begin
(test-->> step
          testTerm-112
          (term (ret (3 12))))
(test-->> step
          testTerm-2
          (term (ret 0)))
))
