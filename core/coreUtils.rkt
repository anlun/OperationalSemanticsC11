#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(provide (all-defined-out))

(define-metafunction coreLang
  getη : auxξ -> η
  [(getη (θ_0 ... η θ_1 ...)) η])

(define-metafunction coreLang
  getReadψ  : auxξ -> ψ
  [(getReadψ (θ_0 ...  (Read ψ)  θ_1 ...)) ψ])

(define-metafunction coreLang
  getWriteψ : auxξ -> ψ
  [(getWriteψ (θ_0 ... (Write ψ) θ_1 ...)) ψ])

(define-metafunction coreLang
  getσSC : auxξ -> σ
  [(getσSC (θ_0 ... (SC σ) θ_1 ...)) σ])

(define-metafunction coreLang
  getGR : auxξ -> G
  [(getGR (θ_0 ... (Graph G) θ_1 ...)) G])

(define-metafunction coreLang
  getGF : auxξ -> GF
  [(getGF (θ_0 ... (GFront GF) θ_1 ...)) GF])

(define-metafunction coreLang
  updateState : θ θ auxξ -> auxξ
  [(updateState θ_old θ_new (θ_0 ... θ_old θ_1 ...)) (θ_0 ... θ_new θ_1 ...)])

#|
(define-metafunction coreLang
  updateStateF : θ (θ -> θ) auxξ -> auxξ
  [(updateStateF θ_old f (θ_0 ... θ_old θ_1 ...)) (θ_0 ... (f θ_old) θ_1 ...)])
|#

(define-metafunction coreLang
  dup : path any -> any
  [(dup ()            any         ) (par any any)]
  [(dup (L path) (par any_0 any_1)) (par (dup path any_0) any_1)]
  [(dup (R path) (par any_0 any_1)) (par any_0 (dup path any_1))])

(define-metafunction coreLang
  join : path ψ -> any
  [(join ()       (par σ_0 σ_1)) (frontMerge σ_0 σ_1)]
  [(join (L path) (par ψ_0 ψ_1)) (par (join path ψ_0) ψ_1)]
  [(join (R path) (par ψ_0 ψ_1)) (par ψ_0 (join path ψ_1))])

(define-metafunction coreLang
  [(getByPath () any) any]
  [(getByPath (L path) (par any_0 any_1)) (getByPath path any_0)]
  [(getByPath (R path) (par any_0 any_1)) (getByPath path any_1)])

(define-metafunction coreLang
  updateByFront : path σ ψ -> ψ
  [(updateByFront ()       σ_delta            σ)  (frontMerge σ_delta σ)]
  [(updateByFront (L path) σ_delta (par ψ_0 ψ_1)) (par (updateByFront path σ_delta ψ_0) ψ_1)]
  [(updateByFront (R path) σ_delta (par ψ_0 ψ_1)) (par ψ_0 (updateByFront path σ_delta ψ_1))])

(define-metafunction coreLang
  seeLast : ι η σ -> boolean
  [(seeLast ι η σ) ,(equal? (term τ) (term (fromMaybe -1 (lookup ι σ))))
                   (where τ (getLastTimestamp ι η))])

(define-metafunction coreLang
  dontSeeLast : ι η σ -> boolean
  [(dontSeeLast ι η σ) ,(not (term (seeLast ι η σ)))])

(define-relation coreLang
  negativeτ ⊆ τ
  [(negativeτ τ)
   ,(< (term τ) 0)])

(define-relation coreLang
  nonNegativeτ ⊆ τ
  [(nonNegativeτ τ)
   ,(not (term (negativeτ τ)))])

(define-metafunction coreLang
  getReadσ : path auxξ -> σ
  [(getReadσ path auxξ) (getByPath path (getReadψ auxξ))])

(define-relation coreLang
  failCAScondition ⊆ ι × η × μ-value × SM × FM
  [(failCAScondition ι η μ-value SM FM)
   (nonNegativeτ (getLastTimestamp ι η))
   ,(not (equal?
          (term μ-value)
          (term (getValueByCorrectTimestamp ι (getLastTimestamp ι η) η))))
   (casMO=>? SM FM)])

(define-relation coreLang
  succCAScondition ⊆ ι × η × μ-value × SM × FM
  [(succCAScondition ι η μ-value SM FM)
   (nonNegativeτ (getLastTimestamp ι η))
   ,(equal? (term μ-value)
            (term (getValueByCorrectTimestamp ι (getLastTimestamp ι η) η)))
   (casMO=>? SM FM)])

(define-metafunction coreLang
  updateReadσ : path σ auxξ -> auxξ
  [(updateReadσ path σ auxξ)
   (updateState (Read ψ) (Read ψ_new) auxξ)
   (where ψ     (getReadψ auxξ))
   (where ψ_new (updateByFront path σ ψ))])

(define-metafunction coreLang
  getWriteσ_2ψ : path auxξ -> σ
  [(getWriteσ_2ψ path auxξ) (getByPath path (getWriteψ auxξ))])

(define-metafunction coreLang
  synchronizeWriteFront : path auxξ -> auxξ
  [(synchronizeWriteFront path auxξ)
   (updateState (Write ψ_write) (Write ψ_write_new) auxξ)
   (where ψ_read      (getReadψ auxξ))
   (where σ           (getByPath path ψ_read))
   (where ψ_write     (getWriteψ auxξ))
   (where ψ_write_new (updateByFront path σ ψ_write))])

(define-metafunction coreLang
  spwST_readψ : path auxξ -> auxξ
  [(spwST_readψ path auxξ) (updateState (Read ψ_old) (Read (dup path ψ_old)) auxξ)
                           (where ψ_old (getReadψ auxξ))])

(define-metafunction coreLang
  joinST_readψ : path auxξ -> auxξ
  [(joinST_readψ path auxξ) (updateState (Read ψ_old) (Read (join path ψ_old)) auxξ)
                            (where ψ_old (getReadψ auxξ))])

(define-metafunction coreLang
  spwST_writeψ : path auxξ -> auxξ
  [(spwST_writeψ path auxξ) (updateState (Write ψ_old) (Write (dup path ψ_old)) auxξ)
                            (where ψ_old (getWriteψ auxξ))])

(define-metafunction coreLang
  joinST_writeψ : path auxξ -> auxξ
  [(joinST_writeψ path auxξ) (updateState (Write ψ_old) (Write (join path ψ_old)) auxξ)
                             (where ψ_old (getWriteψ auxξ))])

(define-metafunction coreLang
  getWriteσ_nil : path auxξ -> σ
  [(getWriteσ_nil path auxξ) ()])

(define-metafunction coreLang
  synchronizeWriteFront_id : path auxξ -> auxξ
  [(synchronizeWriteFront_id path auxξ) auxξ])

; Maybe for `2ψ` rules we should add synchronization between write
; and read fronts.

(define-metafunction coreLang
  spwST_2ψ : path auxξ -> auxξ
  [(spwST_2ψ  path auxξ) (spwST_writeψ  path (spwST_readψ  path auxξ))])

(define-metafunction coreLang
  joinST_2ψ : path auxξ -> auxξ
  [(joinST_2ψ path auxξ) (joinST_writeψ path (joinST_readψ path auxξ))])

;; Postponed reads part

(define-metafunction coreLang
  getφ : auxξ -> φ
  [(getφ (θ_0 ... (P φ) θ_1 ...)) φ])

(define-metafunction coreLang
  pathEp : Ep -> path
  [(pathEp hole) ()]
  [(pathEp (par Ep φ)) (L (pathEp Ep))]
  [(pathEp (par φ Ep)) (R (pathEp Ep))])

(define-metafunction coreLang
  updateOnPath : path any any -> any
  [(updateOnPath ()       any_new              any)  any_new]
  [(updateOnPath (L path) any_new (par any_0 any_1)) (par (updateOnPath path any_new any_0) any_1)]
  [(updateOnPath (R path) any_new (par any_0 any_1)) (par any_0 (updateOnPath path any_new any_1))])

(define-metafunction coreLang
  spwST_readψ_φ : path auxξ -> auxξ
  [(spwST_readψ_φ path auxξ) (updateState (P φ_old) (P (dup path φ_old)) auxξ_readψ)
                             (where auxξ_readψ (spwST_readψ path auxξ))
                             (where φ_old (getφ auxξ_readψ))])

(define-metafunction coreLang
  joinST_readψ_φ : path auxξ -> auxξ
  [(joinST_readψ_φ path auxξ) (updateState (P φ_old) (P φ_new) auxξ_readψ)
                              (where auxξ_readψ (joinST_readψ path auxξ))
                              (where φ_old      (getφ auxξ_readψ))
                              (where φ_new      (updateOnPath path () φ_old))])

(define-metafunction coreLang
  spwST_2ψ_φ : path auxξ -> auxξ
  [(spwST_2ψ_φ path auxξ) (updateState (P φ_old) (P (dup path φ_old)) auxξ_2ψ)
                          (where auxξ_2ψ (spwST_2ψ path auxξ))
                          (where φ_old   (getφ auxξ_2ψ))])

(define-metafunction coreLang
  joinST_2ψ_φ : path auxξ -> auxξ
  [(joinST_2ψ_φ path auxξ) (updateState (P φ_old) (P φ_new) auxξ_2ψ)
                           (where auxξ_2ψ (joinST_2ψ path auxξ))
                           (where φ_old   (getφ auxξ_2ψ))
                           (where φ_new   (updateOnPath path () φ_old))])

(define (getLastNodeNumber nodes)
      (apply max
             (map (lambda (x)
                    (match x [(list fst snd) fst]))
             nodes)))

(define (getLastNodeNumber_gr graph)
  (match graph [(list nodes edges)
      (getLastNodeNumber nodes)]))

(define (getNextNodeNumber nodes)
  (+ 1 (getLastNodeNumber nodes)))

(define (getNextNodeNumber_gr graph)
  (+ 1 (getLastNodeNumber_gr graph)))

(define-metafunction coreLang
  joinST_gr : path auxξ -> auxξ
  [(joinST_gr path auxξ) (updateState (Graph G) (Graph G_new)
                             (updateState (GFront GF) (GFront GF_new) auxξ))
                         
                         (where G (getGR auxξ))
                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_join (number_new skip))
                         
                         (where GF (getGF auxξ))
                         (where (par number_left number_right) (getByPath path GF))
                         
                         (where Nodes_new ,(cons   (term Node_join) (term Nodes)))
                         (where Edges_new ,(append
                                            (term
                                             ((number_left  number_new asw)
                                              (number_right number_new asw)))
                                            (term Edges)))
                         (where G_new (Nodes_new Edges_new))
                         
                         (where GF_new (updateOnPath path number_new GF))])

(define-metafunction coreLang
  spwST_gr : path auxξ -> auxξ
  [(spwST_gr path auxξ) (updateState (Graph G) (Graph G_new)
                            (updateState (GFront GF) (GFront GF_new) auxξ))
                        
                         (where G (getGR auxξ))
                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_fork (number_new skip))
                         
                         (where GF (getGF auxξ))
                         (where number_current (getByPath path GF))
                         
                         (where Nodes_new ,(cons (term Node_fork) (term Nodes)))
                         (where G_new (Nodes_new Edges))
                         (where GF_new (updateOnPath path (par number_new number_new) GF))])

(define-metafunction coreLang
  isReadQueueEqualTo : φ path auxξ -> boolean
  [(isReadQueueEqualTo φ path auxξ) ,(equal? (term φ) (term φ_path))
                                           (where φ_all (getφ auxξ))
                                           (where φ_path (getByPath path φ_all))])

(define-metafunction coreLang
  isReadQueueEqualTo_t : φ path auxξ -> boolean
  [(isReadQueueEqualTo_t φ path auxξ) #t])

(define-metafunction coreLang
  ιNotInα : ι α -> boolean
  [(ιNotInα ι (any_0 ... (vName         ι RM) any_1 ...)) #f]
  [(ιNotInα ι (any_0 ... (vName_0 vName_1 RM) any_1 ...)) #f]
  [(ιNotInα ι α)                                          #t])

(define-metafunction coreLang
  ιNotInReadQueue : ι path auxξ -> boolean
  [(ιNotInReadQueue ι path auxξ) (ιNotInα ι α)
                                 (where φ (getφ auxξ))
                                 (where α (getByPath path φ))])
(define-metafunction coreLang
  ιNotInReadQueue_t : ι path auxξ -> boolean
  [(ιNotInReadQueue_t ι path auxξ) #t])

(define-metafunction coreLang
  isFirstRecord : vName ι α -> boolean
  [(isFirstRecord vName_0 ι_0 ((vName_0 ι_0     RM ) any ...)) #t]
  [(isFirstRecord vName_0 ι_0 ((vName_1 ι_1     acq) any ...)) #f]
  [(isFirstRecord vName_0 ι   ((vName_1 vName_2 RM ) any ...)) #f]
  [(isFirstRecord vName_0 ι_0 ((vName_1 ι_1     RM ) any ...)) (isFirstRecord vName_0 ι_0 (any ...))])

(define-metafunction coreLang
  substμα : vName μ-value α -> α
  [(substμα vName ι       α) (substια vName ι α)]
  [(substμα vName μ-value α) α])

(define-metafunction coreLang
  substια : vName ι α -> α
  [(substια vName   ι ()) ()]
  [(substια vName_0 ι ((vName_1 ι-var RM) any ...))
   ,(cons (term (vName_1 (substι vName_0 ι ι-var) RM))
          (term (substια vName_0 ι (any ...))))])

(define-metafunction coreLang
  isLocationUninitialized : ι-var auxξ -> boolean
  [(isLocationUninitialized ι auxξ) ,(equal? (term (getLastTimeStamp ι η)) (term -1))
                                    (where η (getη auxξ))]
  [(isLocationUninitialized vName auxξ) #f])

;;;;;;;;;;;;;;;;;
; Tests
;;;;;;;;;;;;;;;;;
(define (coreUtils-tests)
  (test-equal
   (getLastNodeNumber_gr (term (((1 skip)) ())))
   1)
  (test-equal
   (getLastNodeNumber_gr
    (term (((1 skip) (4 (read rlx x 10)) (5 (write rlx y 34))) ())))
   5)
  
  (test-equal
   (term (spwST_gr () (() (Graph (((0 skip)) ())) (GFront 0))))
   (term (() (Graph (((1 skip) (0 skip)) ())) (GFront (par 1 1))))))
(coreUtils-tests)