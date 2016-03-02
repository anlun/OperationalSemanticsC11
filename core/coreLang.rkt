#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(provide coreLang define-coreStep define-coreTest normalize isUsed
         isPossibleE isPossiblePath
         isPossibleRead
         isLocationDeallocated

         getη isLocationUninitialized)

(define-extended-language coreLang syntax
  ; State:
  ; AST -- current state of program tree;
  ; θ   -- auxiliary state.
  [θ any]
  [auxξ (θ ... η θ ...)]
  [ξ (AST auxξ)])

(define-metafunction coreLang
  getη : auxξ -> η
  [(getη (θ_0 ... η θ_1 ...)) η])

(define-metafunction coreLang
  isPossiblePath : path auxξ -> boolean
  [(isPossiblePath path_0 (θ_0 ... (Paths ((path_1 τ_1) (path_2 τ_2) ...)) θ_1 ...))
   ,(equal? (term path_0) (term path_1))]
  [(isPossiblePath path (θ_0 ... (Paths ()) θ_1 ...))
   #f]
  [(isPossiblePath path auxξ) #t])

(define-metafunction coreLang
  isPossibleE : E auxξ -> boolean
  [(isPossibleE E auxξ) (isPossiblePath (pathE E) auxξ)])

(define-metafunction coreLang
  ;; isPossibleRead : (E | path) τ τ auxξ -> boolean 
  [(isPossibleRead path_0 τ_front τ_read
                   (θ_0 ... (Paths ((path_1 τ_1) (path_2 τ_2) ...)) θ_1 ...))
   ,(and (equal? (term path_0) (term path_1))
         (equal? (term τ_read) (+ (term τ_front)
                                  (term τ_1))))]

  [(isPossibleRead E τ_front τ_read
                   (θ_0 ... (Paths ((path_1 τ_1) (path_2 τ_2) ...)) θ_1 ...))
   ,(and (equal? (term path_0) (term path_1))
         (equal? (term τ_read) (+ (term τ_front)                                  
                                  (term τ_1))))
   (where path_0 (pathE E))]
  [(isPossibleRead any τ_0 τ_1
                   (θ_0 ... (Paths ()) θ_1 ...)) #f]
  [(isPossibleRead any τ_0 τ_1 auxξ) #t])

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

   [(normalize_subst
     ((in-hole E (in-hole EU        (op ι Expr)))  auxξ))
   (normalize_subst
     ((in-hole E (in-hole EU (calcι (op ι Expr)))) auxξ))] 

   [(normalize_subst
     ((in-hole E (in-hole EU        (op Expr ι)))  auxξ))
   (normalize_subst
     ((in-hole E (in-hole EU (calcι (op Expr ι)))) auxξ))] 
 
  [(normalize_subst
     ((in-hole E (in-hole EU       (op number_1 number_2)))  auxξ))
   (normalize_subst
     ((in-hole E (in-hole EU (calc (op number_1 number_2)))) auxξ))
   (side-condition (not (equal? (term op) 'choice)))]
  
  [(normalize_subst
     ((in-hole E (in-hole EU           (projOp (μ_1 μ_2))))  auxξ))
   (normalize_subst
     ((in-hole E (in-hole EU (projCalc (projOp (μ_1 μ_2))))) auxξ))]
  [(normalize_subst ξ) ξ])

(define-metafunction coreLang
  schedulerStep : auxξ -> auxξ
  [(schedulerStep (θ_0 ... (Paths ()) θ_1 ...))
   (θ_0 ... (Paths ()) θ_1 ...)]
  [(schedulerStep (θ_0 ... (Paths pathsτ) θ_1 ...))
   (θ_0 ... (Paths ,(cdr (term pathsτ))) θ_1 ...)]
  [(schedulerStep auxξ) auxξ])

(define-metafunction coreLang
  normalize : ξ -> ξ
  [(normalize (AST auxξ)) (normalize_subst (AST (schedulerStep auxξ)))])

(define-metafunction coreLang
  isLocationDeallocated : ι-var auxξ -> boolean
  [(isLocationDeallocated ι (θ_0 ... (Deallocated listι) θ_1 ...))
   ,(not (false? (member (term ι) (term listι))))]
  [(isLocationDeallocated ι-var auxξ) #f])

(define-metafunction coreLang
  deallocate : ι auxξ -> auxξ
  [(deallocate ι (θ_0 ... (Deallocated listι) θ_1 ...))
   (θ_0 ... (Deallocated ,(cons (term ι) (term listι))) θ_1 ...)])

(define-metafunction coreLang
  isLocationUninitialized : ι-var auxξ -> boolean
  [(isLocationUninitialized ι auxξ) ,(equal? (term (getLastTimestamp ι η)) (term -1))
                                    (where η (getη auxξ))]
  [(isLocationUninitialized vName auxξ) #f])

; ST stands for `state transformer`.
(define-syntax-rule (define-coreStep defaultState spwST joinST isReadQueueEqualTo)
  (begin

  (reduction-relation coreLang #:domain ξ

   (-->  ((in-hole E ((ret μ-subst) >>= (λ vName AST))) auxξ)
        (normalize
         ((in-hole E (subst vName μ-subst AST))         auxξ))
        ">>=-subst"
        (side-condition (term (isPossibleE E auxξ))))
   
   (-->  ((in-hole E (in-hole EU (choice number_1 number_2))) auxξ)
        (normalize
         ((in-hole E (in-hole EU         number_1          )) auxξ))
        "num-choice-left"
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (in-hole EU (choice number_1 number_2))) auxξ)
        (normalize
         ((in-hole E (in-hole EU                  number_2 )) auxξ))
        "num-choice-right"
        (side-condition (term (isPossibleE E auxξ))))
  
   (-->  ((in-hole E (                            repeat AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeat AST))))) auxξ))
        "repeat-unroll"
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (                            repeatFuel number     AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeatFuel number_new AST))))) auxξ))
        "repeatFuel-unroll"
        (where number_new ,(- (term number) 1))
        (side-condition
         (> (term number) 0))
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (repeatFuel 0 AST)) auxξ)
        (nofuel defaultState)
        "repeatFuel-nofuel"
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-uninitialized"
        (side-condition (or (term (isLocationUninitialized ι-var auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-uninitialized"
        (side-condition (or (term (isLocationUninitialized ι-var auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (read RM ι-var)) auxξ)
        (stuck defaultState)
        "read-stuck"
        (side-condition (or (term (isLocationDeallocated   ι-var auxξ))
                            (term (isLocationUninitialized ι-var auxξ)))))

   (--> ((in-hole E (readCon RM ι-var σ-dd)) auxξ)
        (stuck defaultState)
        "readCon-stuck"
        (side-condition (or (term (isLocationDeallocated   ι-var auxξ))
                            (term (isLocationUninitialized ι-var auxξ)))))

   (--> ((in-hole E (write WM ι)) auxξ)
        (stuck defaulState)
        "write-stuck" ; segfault
        (side-condition (term (isLocationDeallocated ι-var auxξ))))
  
   (-->  ((in-hole E (if 0 AST_1 AST_2)) auxξ)
        (normalize 
         ((in-hole E AST_2             ) auxξ))
        "if-false"
        (side-condition (term (isPossibleE E auxξ))))
   (-->  ((in-hole E (if number AST_1 AST_2)) auxξ)
        (normalize 
         ((in-hole E AST_1                  ) auxξ))
        "if-true"
        (side-condition
          (not (equal? (term number) 0)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (par (ret μ-value_0) (ret μ-value_1)))              auxξ)
        (normalize 
         ((in-hole E (ret (    μ-value_0       μ-value_1))) (joinST path auxξ)))
        "join"
        (where path (pathE E))
        (side-condition (term (isReadQueueEqualTo (par () ()) path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (spw AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E (par AST_0 AST_1)) auxξ_new))
        "spw"
        (where path (pathE E))
        (where auxξ_new (spwST path auxξ))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
     
   ; For test results brevity only.
   (--> ((ret μ) auxξ)
        ((ret μ) defaultState)
        "heap-info-erasure"
        (side-condition     ; To eliminate cycle.
         (not (equal? (term auxξ) (term defaultState)))))
        ;; (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (dealloc ι)) auxξ)
        (normalize
         ((in-hole E (ret     0)) auxξ_new))
        "deallocate"
        (where auxξ_new (deallocate ι auxξ))
        (side-condition (not (term (isLocationDeallocated ι auxξ))))
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (dealloc ι)) auxξ)
        (stuck defaultState)
        "deallocate-stuck"
        (side-condition (term (isLocationDeallocated ι auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
   )))

;;;;;;;;;;;;;;;;
; Test macros
;;;;;;;;;;;;;;;;

(define testTerm-1
  (term ((spw (ret (+ 1 2)) (ret (+ 3 9))) >>= (λ v
          (ret v)))))

(define-syntax-rule (define-coreTest step defaultState)
  (begin
(test-->> step
          (term (,testTerm-1 defaultState))
          (term ((ret (3 12)) defaultState)))))
