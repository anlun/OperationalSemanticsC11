#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(provide (all-defined-out))

(define-metafunction coreLang
  getη : auxξ -> η
  [(getη (θ_0 ... η θ_1 ...)) η])

(define-metafunction coreLang
  getObservedWrites : auxξ -> observedWrites
  [(getObservedWrites (θ_0 ... (RW observedWrites) θ_1 ...)) observedWrites])

(define-metafunction coreLang
  updateState : θ θ auxξ -> auxξ
  [(updateState θ_old θ_new (θ_0 ... θ_old θ_1 ...)) (θ_0 ... θ_new θ_1 ...)])

(define-metafunction coreLang
  holeIndex : El -> number
  [(holeIndex (any_0 ... hole any_1 ...)) ,(length (term (any_0 ...)))])

(define-relation syntax
  correctτ ⊆ τ × ι × σ
  [(correctτ τ ι σ)
   ,(not (equal? (term None) (term (lookup ι σ))))     ; This condition check if location is mentioned in front.
   ,(>= (term τ) (term (fromMaybe -1 (lookup ι σ))))])

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
  getσNA : auxξ -> σ
  [(getσNA (θ_0 ... (NA σ) θ_1 ...)) σ])

(define-metafunction coreLang
  getGR : auxξ -> G
  [(getGR (θ_0 ... (Graph G) θ_1 ...)) G])

(define-metafunction coreLang
  getGF : auxξ -> GF
  [(getGF (θ_0 ... (GFront GF) θ_1 ...)) GF])

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
  spwST-readψ : path auxξ -> auxξ
  [(spwST-readψ path auxξ) (updateState (Read ψ_old) (Read (dup path ψ_old)) auxξ)
                           (where ψ_old (getReadψ auxξ))])

(define-metafunction coreLang
  joinST-readψ : path auxξ -> auxξ
  [(joinST-readψ path auxξ) (updateState (Read ψ_old) (Read (join path ψ_old)) auxξ)
                            (where ψ_old (getReadψ auxξ))])

(define-metafunction coreLang
  spwST-writeψ : path auxξ -> auxξ
  [(spwST-writeψ path auxξ) (updateState (Write ψ_old)
                                         (Write (updateOnPath path (par () ()) ψ_old))
                                         auxξ)
                            (where ψ_old (getWriteψ auxξ))])

(define-metafunction coreLang
  joinST-writeψ : path auxξ -> auxξ
  [(joinST-writeψ path auxξ) (updateState (Write ψ_old)
                                          (Write (updateOnPath path () ψ_old))
                                          auxξ)
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
  spwST-2ψ : path auxξ -> auxξ
  [(spwST-2ψ  path auxξ) (spwST-writeψ  path (spwST-readψ  path auxξ))])

(define-metafunction coreLang
  joinST-2ψ : path auxξ -> auxξ
  [(joinST-2ψ path auxξ) (joinST-writeψ path (joinST-readψ path auxξ))])

;; Postponed reads part

(define-metafunction coreLang
  getφ : auxξ -> φ
  [(getφ (θ_0 ... (P φ) θ_1 ...)) φ])

(define-metafunction coreLang
  getγ : auxξ -> γ
  [(getγ (θ_0 ... (R γ) θ_1 ...)) γ])

(define-metafunction coreLang
  pathEp : Ep -> path
  [(pathEp hole) ()]
  [(pathEp (par Ep φ)) (L (pathEp Ep))]
  [(pathEp (par φ Ep)) (R (pathEp Ep))])

(define-metafunction coreLang
  ;updatePath : (L | R) path -> path
  updatePath : any path -> path
  [(updatePath any ()) (any ())]
  [(updatePath any_0 (any_1 path)) (any_1 (updatePath any_0 path))])

(define-metafunction coreLang
  updateOnPath : path any any -> any
  [(updateOnPath ()       any_new              any)  any_new]
  [(updateOnPath (L path) any_new (par any_0 any_1))
   (par (updateOnPath path any_new any_0) any_1)]
  [(updateOnPath (R path) any_new (par any_0 any_1))
   (par any_0 (updateOnPath path any_new any_1))])

(define-metafunction coreLang
  spwST-readψ-φ : path auxξ -> auxξ
  [(spwST-readψ-φ path auxξ) (updateState (P φ_old) (P (dup path φ_old)) auxξ_readψ)
                             (where auxξ_readψ (spwST-readψ path auxξ))
                             (where φ_old (getφ auxξ_readψ))])

(define-metafunction coreLang
  joinST-readψ-φ : path auxξ -> auxξ
  [(joinST-readψ-φ path auxξ) (updateState (P φ_old) (P φ_new) auxξ_readψ)
                              (where auxξ_readψ (joinST-readψ path auxξ))
                              (where φ_old      (getφ auxξ_readψ))
                              (where φ_new      (updateOnPath path () φ_old))])
;; (RW observedWrites)
(define-metafunction coreLang
  spwST-2ψ-φ : path auxξ -> auxξ
  [(spwST-2ψ-φ path auxξ) auxξ_new
                          (where auxξ_2ψ  (spwST-2ψ path auxξ))
                          (where φ_old    (getφ auxξ_2ψ))
                          (where auxξ_φ   (updateState (P φ_old) (P (dup path φ_old)) auxξ_2ψ))

                          (where observedWrites_old (getObservedWrites auxξ_φ))
                          (where auxξ_new (updateState (RW observedWrites_old)
                                                       (RW (dup path observedWrites_old))
                                                       auxξ_φ))])

(define-metafunction coreLang
  joinST-2ψ-φ : path auxξ -> auxξ
  [(joinST-2ψ-φ path auxξ) auxξ_new
                           (where auxξ_2ψ (joinST-2ψ path auxξ))
                           (where φ_old   (getφ auxξ_2ψ))
                           (where φ_new   (updateOnPath path () φ_old))
                           (where auxξ_φ  (updateState (P φ_old) (P φ_new) auxξ_2ψ))

                           (where observedWrites_old (getObservedWrites auxξ_φ))
                           (where observedWrites_new (updateOnPath path () observedWrites_old))
                           (where auxξ_new (updateState (RW observedWrites_old)
                                                        (RW observedWrites_new)
                                                        auxξ_φ))])

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
  joinST-gr : path auxξ -> auxξ
  [(joinST-gr path auxξ) (updateState (Graph G) (Graph G_new)
                             (updateState (GFront GF) (GFront GF_new) auxξ))
                         
                         (where G (getGR auxξ))
                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_join (number_new skip))
                         
                         (where GF (getGF auxξ))
                         (where (par number_left number_right) (getByPath path GF))
                         
                         (where Nodes_new ,(cons (term Node_join) (term Nodes)))
                         (where Edges_new ,(append
                                            (term
                                             ((number_left  number_new sb)
                                              (number_right number_new sb)))
                                            (term Edges)))
                         (where G_new (Nodes_new Edges_new))
                         
                         (where GF_new (updateOnPath path number_new GF))])

(define-metafunction coreLang
  spwST-gr : path auxξ -> auxξ
  [(spwST-gr path auxξ) (updateState (Graph G) (Graph G_new)
                            (updateState (GFront GF) (GFront GF_new) auxξ))
                        
                         (where G (getGR auxξ))
                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_fork (number_new skip))
                         
                         (where GF (getGF auxξ))
                         (where number_old (getByPath path GF))
                         (where Edges_new ,(cons
                                            (term (number_old number_new sb))
                                            (term Edges)))
                         
                         (where Nodes_new ,(cons (term Node_fork) (term Nodes)))
                         (where G_new (Nodes_new Edges_new))
                         (where GF_new (updateOnPath path (par number_new number_new) GF))])

(define-metafunction coreLang
  joinST-readψ-gr : path auxξ -> auxξ
  [(joinST-readψ-gr path auxξ) (joinST-gr path (joinST-readψ path auxξ))])

(define-metafunction coreLang
  spwST-readψ-gr : path auxξ -> auxξ
  [(spwST-readψ-gr path auxξ) (spwST-gr path (spwST-readψ path auxξ))])

(define-metafunction coreLang
  addReadNode_t : τ Action path auxξ -> auxξ
  [(addReadNode_t τ Action path auxξ) auxξ])

(define-metafunction coreLang
  addWriteNode_t : Action path auxξ -> auxξ
  [(addWriteNode_t Action path auxξ) auxξ])

(define-metafunction coreLang
  addWriteNode : Action path auxξ -> auxξ
  [(addWriteNode (write WM ι μ-value τ) path auxξ)
                 (updateState (Graph G) (Graph G_new)
                     (updateState (GFront GF) (GFront GF_new) auxξ))
                     (where G (getGR auxξ))
                     (where (Nodes Edges) G)
                     (where number_new ,(getNextNodeNumber (term Nodes)))                   
                     (where Node_write
                            (number_new (write WM ι μ-value τ)))
  
                     (where GF (getGF auxξ))
                     (where number_old (getByPath path GF))
                     (where Nodes_new ,(cons (term Node_write) (term Nodes)))
                     (where Edges_new ,(cons (term (number_old number_new sb))
                                             (term Edges)))                                         
                     (where G_new  (Nodes_new Edges_new))
                     (where GF_new (updateOnPath path number_new GF))])

(define-metafunction coreLang
  isReadQueueEqualTo : φ path auxξ -> boolean
  [(isReadQueueEqualTo φ path auxξ) ,(equal? (term φ) (term φ_path))
                                           (where φ_all (getφ auxξ))
                                           (where φ_path (getByPath path φ_all))])

(define-metafunction coreLang
  isReadQueueEqualTo_t : φ path auxξ -> boolean
  [(isReadQueueEqualTo_t φ path auxξ) #t])


(define-metafunction coreLang
  isPostRlx : postponedEntry -> boolean
  [(isPostRlx (read   vName ι-var rlx σ-dd)) #t]
  [(isPostRlx (read   vName ι-var con σ-dd)) #t]  ; TODO: rename methods appropriately
  [(isPostRlx (let-in vName μ))              #t]
  ;; [(isPostRlx (write  vName ι-var rlx μ   )) #t]
  [(isPostRlx (write  vName ι-var rlx μ   )) #f]
  [(isPostRlx (if vName μ α_0 α_1))
   ,(and (term (are∀PostRlxInα α_0))
         (term (are∀PostRlxInα α_1)))]
  [(isPostRlx any)                           #f])

(define-metafunction coreLang
  are∀PostRlxInα : α -> boolean
  [(are∀PostRlxInα α) ,(andmap (λ (x) (term (isPostRlx ,x))) (term α))])

(define-metafunction coreLang
  are∀PostReadsRlx : path auxξ -> boolean
  [(are∀PostReadsRlx path (θ_0 ... (P φ_all) θ_1 ...)) (are∀PostRlxInα α)
                                                       (where α (getByPath path φ_all))]
  [(are∀PostReadsRlx path auxξ) #t])

(define-metafunction coreLang
  ιNotInPostponedEntry : ι postponedEntry -> boolean
  [(ιNotInPostponedEntry ι (read  vName         ι RM σ-dd)) #f]
  [(ιNotInPostponedEntry ι (read  vName_0 vName_1 RM σ-dd)) #f]
  [(ιNotInPostponedEntry ι (write vName   ι       WM μ   )) #f]
  [(ιNotInPostponedEntry ι (write vName_0 vName_1 WM μ   )) #f]

  [(ιNotInPostponedEntry ι (if vName μ α_0 α_1))
   ,(and (term (ιNotInα ι α_0))
         (term (ιNotInα ι α_1)))]

  [(ιNotInPostponedEntry ι postponedEntry)                  #t])

(define-metafunction coreLang
  ιNotInα : ι α -> boolean
  [(ιNotInα ι α) ,(andmap (λ (x) (term (ιNotInPostponedEntry ι ,x))) (term α))])
   
(define-metafunction coreLang
  ιNotInReadQueue : ι path auxξ -> boolean
  [(ιNotInReadQueue ι path (θ_0 ... (P φ) θ_1 ...))
                                 (ιNotInα ι α)
                                 (where α (getByPath path φ))]
  [(ιNotInReadQueue ι path auxξ) #t])


(define-metafunction coreLang
  αToγRecords : ι τ α -> γ
  [(αToγRecords ι τ α) ,(apply
                         append (map
                                 (λ (x) (match x [(list rd vName locvar mod ddFront)
                                                  (list (list (term ι) (term τ) vName))]
                                                 [_ (list)]))
                                 (term α)))])

(define-metafunction coreLang
  addPostReadsToγ : path ι τ auxξ -> auxξ
  [(addPostReadsToγ path ι τ (θ_0 ... (P φ) θ_1 ... (R γ) θ_2 ...))
   (θ_0 ... (P φ) θ_1 ... (R γ_new) θ_2 ...)
   (where α (getByPath path φ))
   (where γ_new ,(append (term (αToγRecords ι τ α)) (term γ)))]
  [(addPostReadsToγ path ι τ auxξ) auxξ])

(define-metafunction coreLang
  consT : any (any ...) -> (any ...)
  [(consT any_0 any_1) ,(cons (term any_0) (term any_1))])

(define-metafunction coreLang
  appendT : (any ...) (any ...) -> (any ...)
  [(appendT any_0 any_1) ,(append (term any_0) (term any_1))])

(define-metafunction coreLang
  appendT3 : (any ...) (any ...) (any ...) -> (any ...)
  [(appendT3 any_0 any_1 any_2) ,(append (term any_0) (term any_1) (term any_2))])

(define-metafunction coreLang
  substμPostponedEntry : vName μ σ-dd postponedEntry -> postponedEntry
  [(substμPostponedEntry vName_0 ι-var σ-dd_0
                         (read vName_1 vName_0 RM σ-dd_1))
   (read vName_1 ι-var RM (frontMerge σ-dd_0 σ-dd_1))]

  [(substμPostponedEntry vName_0 μ_0 σ-dd
                         (let-in vName_1 μ_1))
   (let-in vName_1 (calcμ (substExpr vName_0 μ_0 μ_1)))]

  [(substμPostponedEntry vName_0 μ_0 σ-dd
                         (write vName_1 ι-var WM μ_1))
   (write vName_1 (substExpr vName_0 μ_0 ι-var) WM
           (calcμ (substExpr vName_0 μ_0 μ_1)))]
  
  [(substμPostponedEntry vName_0 μ_0 σ-dd
                         (if vName_1 μ_1 α_0 α_1))
   (if vName_1 (calcμ (substExpr vName_0 μ_0 μ_1))
       (substμα vName_0 μ_0 σ-dd α_0)
       (substμα vName_0 μ_0 σ-dd α_1))]
  
  [(substμPostponedEntry vName_0 μ σ-dd any) any])

(define-metafunction coreLang
  substμα : vName μ σ-dd α -> α

  [(substμα vName μ σ-dd α)
   ,(map (λ (x)
           (term (substμPostponedEntry vName μ σ-dd ,x)))
         (term α))])

(define-metafunction coreLang
  getσToWrite : σ ι η -> σ
  [(getσToWrite σ_write ι η) σ
                             (where (Just τ) (lookup ι σ_write))
                             (where (Just (μ-value σ)) (lookup3 τ (getCellHistory ι η)))]
  [(getσToWrite σ_write ι η) ()])

(define-metafunction coreLang
  dupγ : ι τ τ γ -> γ
  [(dupγ ι τ_new τ_old γ)
   ,(append (term γ_dup) (term γ))
   (where γ_filtered ,(filter (λ (x)
                                (match x
                                  [(list loc t vName)
                                   (and (equal? loc (term ι))
                                        (equal? t   (term τ_old)))]))
                              (term γ)))
   (where γ_dup ,(map (λ (x) (match x
                               [(list loc t vName)
                                (list loc (term τ_new) vName)]))
                      (term γ_filtered)))])

(define-metafunction coreLang
  dupRelWriteRestrictions : ι τ σ auxξ -> auxξ
  [(dupRelWriteRestrictions ι τ_rlx σ_write (θ_0 ... (R γ) θ_1 ...))
   (θ_0 ... (R γ_new) θ_1 ...)
   (where (Just τ_rel) (lookup ι σ_write))
   (where γ_new (dupγ ι τ_rlx τ_rel γ))]
  [(dupRelWriteRestrictions ι τ σ_write auxξ) auxξ])

(define-metafunction coreLang
  eifToIfContext : Eif -> (vName ...)
  [(eifToIfContext Eif1) ()]
  [(eifToIfContext (if vName Eif AST)) (consT vName (eifToIfContext Eif))]
  [(eifToIfContext (if vName AST Eif)) (consT vName (eifToIfContext Eif))])

(define-metafunction coreLang
  pathEif : Eif -> path
  [(pathEif Eif1) ()]
  [(pathEif (if vName Eif AST)) (L (pathEif Eif))]
  [(pathEif (if vName AST Eif)) (R (pathEif Eif))])

(define-metafunction coreLang
  getIfContext : Eifα -> ifContext
  [(getIfContext hole) ()]
  [(getIfContext (postponedEntry_0 ... (if vName Expr Eifα α) postponedEntry_1 ...))
   (consT vName (getIfContext Eifα))]
  [(getIfContext (postponedEntry_0 ... (if vName Expr α Eifα) postponedEntry_1 ...))
   (consT vName (getIfContext Eifα))])

(define-metafunction coreLang
  isCorrectEifIds : (vName ...) path α -> boolean
  [(isCorrectEifIds () () α) #t]
  [(isCorrectEifIds (vName_0 vName_1 ...) (L path) (any_0 ... (if vName_0 Expr α_0 α_1) any_1 ...))
   (isCorrectEifIds (vName_1 ...) path α_0)]
  [(isCorrectEifIds (vName_0 vName_1 ...) (R path) (any_0 ... (if vName_0 Expr α_0 α_1) any_1 ...))
   (isCorrectEifIds (vName_1 ...) path α_1)]
  [(isCorrectEifIds any path α) #f])

(define-metafunction coreLang
  isCorrectEif : Eif α -> boolean
  [(isCorrectEif Eif α) (isCorrectEifIds (eifToIfContext Eif) (pathEif Eif) α)])

(define-metafunction coreLang
  acqFailCASσReadNew : ι η σ -> σ
  [(acqFailCASσReadNew ι η σ_read)
   (frontMerge σ_read σ_record_front)
   
   (where τ_last         (getLastTimestamp ι η))
   (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ_last η)))])

(define-metafunction coreLang
  acqSuccCASσReadNew : ι η σ -> σ
  [(acqSuccCASσReadNew ι η σ_read)
   (updateFront ι τ (acqFailCASσReadNew ι η σ_read))
   (where τ (getNextTimestamp ι η))])

(define-metafunction coreLang
  getDataDependencies_full : μ-value σ η -> σ-dd
  [(getDataDependencies_full ι σ η) ,(cons (term (ι τ))
                                            (term (getDataDependencies_full μ-value σ η)))
                                     (where (Just τ      ) (lookup ι σ))
                                     (where (Just μ-value) (getValueByTimestamp ι τ η))]
  [(getDataDependencies_full μ-value σ η) ()])

(define-metafunction coreLang
  getDataDependencies : μ-value σ η -> σ-dd
  [(getDataDependencies μ-value σ η) ,(cdr
                                       (term (getDataDependencies_full μ-value σ η)))])

(define (getDD-tests)
  (test-equal (term (getDataDependencies "x"
                                   (("x" 1) ("y" 1) ("z" 1))
                                   (("x" ((0 0 ()) (1 "y" ())))
                                    ("y" ((0 0 ()) (1 "z" ())))
                                    ("z" ((0 0 ()) (1  1  ()))))))
              (term (("y" 1) ("z" 1))))

  (test-equal (term (getDataDependencies "p"
                                         (("data" 0) ("p" 0))
                                         (("data" ((1 5 (("data" 1))) (0 0 (("data" 0)))))
                                          ("p"
                                           ((1 "data" (("data" 1) ("p" 1)))
                                            (0 0 (("data" 0) ("p" 0))))))))
              (term ()))

  (test-equal (term (getDataDependencies "p"
                                         (("data" 1) ("p" 1))
                                         (("data" ((1 5 (("data" 1))) (0 0 (("data" 0)))))
                                          ("p"
                                           ((1 "data" (("data" 1) ("p" 1)))
                                            (0 0 (("data" 0) ("p" 0))))))))
              (term (("data" 1)))))
(getDD-tests)

(define-metafunction coreLang
  propagateDD_helpF : σ-dd vName AST -> AST

  [(propagateDD_helpF σ-dd vName (read RM vName))
   (readCon RM vName σ-dd)]

  [(propagateDD_helpF σ-dd_0 vName (readCon RM vName σ-dd_1))
   (readCon RM vName (frontMerge σ-dd_0 σ-dd_1))]

  [(propagateDD_helpF σ-dd vName (cas SM FM vName μ_0 μ_1))
   (casCon SM FM vName μ_0 μ_1 σ-dd)]

  [(propagateDD_helpF σ-dd_0 vName (casCon SM FM vName μ_0 μ_1 σ-dd_1))
   (casCon SM FM vName μ_0 μ_1 (frontMerge σ-dd_0 σ-dd_1))]

  [(propagateDD_helpF σ-dd vName (if Expr AST_0 AST_1))
   (if Expr
       (propagateDD_helpF σ-dd vName AST_0)
       (propagateDD_helpF σ-dd vName AST_1))]

  [(propagateDD_helpF σ-dd vName (repeat AST))
   (repeat
       (propagateDD_helpF σ-dd vName AST))]

  [(propagateDD_helpF σ-dd vName (repeatFuel number AST))
   (repeatFuel number (propagateDD_helpF vName σ-dd AST))]

  [(propagateDD_helpF σ-dd vName_0 (AST_0 >>= (λ vName_1 AST_1)))
   ((propagateDD_helpF σ-dd vName_0 AST_0) >>=
    (λ vName_1 (propagateDD_helpF σ-dd vName_0 AST_1)))   
   (side-condition (not (equal? (term vName_0) (term vName_1))))]

  [(propagateDD_helpF σ-dd vName (AST_0 >>= (λ vName AST_1)))
   ((propagateDD_helpF σ-dd vName AST_0) >>=
    (λ vName AST_1))]
  
  [(propagateDD_helpF σ-dd vName AST) AST])

;; DD -- data dependencies
(define-metafunction coreLang
  propagateDD : path σ-dd AST -> AST
  [(propagateDD () σ-dd ((ret μ-value) >>= (λ vName AST)))
   ((ret μ-value) >>= (λ vName (propagateDD_helpF σ-dd vName AST)))]
  
  [(propagateDD path σ-dd (AST_0 >>= (λ vName AST_1)))
   ((propagateDD path σ-dd AST_0) >>= (λ vName AST_1))]

  [(propagateDD (L path) σ-dd (par AST_0 AST_1))
   (par (propagateDD path σ-dd AST_0) AST_1)]
  [(propagateDD (R path) σ-dd (par AST_0 AST_1))
   (par AST_0 (propagateDD path σ-dd AST_1))]

  [(propagateDD path σ-dd AST) AST])

(define-metafunction coreLang
  propagateDD_vName : vName path σ-dd AST -> AST
  [(propagateDD_vName vName (L path) σ-dd (par AST_0 AST_1))
   (par (propagateDD_vName vName path σ-dd AST_0) AST_1)]

  [(propagateDD_vName vName (R path) σ-dd (par AST_0 AST_1))
   (par AST_0 (propagateDD_vName vName path σ-dd AST_1))]

  [(propagateDD_vName vName_0 path σ-dd ((ret vName_0) >>= (λ vName_1 AST_1)))
   ((ret vName_0) >>= (λ vName_1 (propagateDD_vName vName_1 path σ-dd AST_1)))]

  [(propagateDD_vName vName_0 path σ-dd (AST_0 >>= (λ vName_1 AST_1)))
   ((propagateDD_vName vName_0 path σ-dd AST_0) >>= (λ vName_1 AST_1))]

  [(propagateDD_vName vName () σ-dd (if Expr AST_0 AST_1))
   (if Expr
       (propagateDD_vName vName () σ-dd AST_0)
       (propagateDD_vName vName () σ-dd AST_1))]

  [(propagateDD_vName vName () σ-dd AST)
   (propagateDD_helpF σ-dd vName AST)])

(define (propagateDD-tests)
  (test-equal (term (propagateDD (R ())
                                 ()
                                 ((par (ret 0)
                                       ((ret 0) >>=
                                        (λ r1 (read na r1)))) >>=
                                  (λ r0 (ret r0)))))
              '((par (ret 0) ((ret 0) >>= (λ r1 (readCon na r1 ()))))
                >>=
                (λ r0 (ret r0))) ))

(propagateDD-tests)

(define (find-path red from to)
  (define parents (make-hash))
  (let/ec done
    (let loop ([t from])
      (define nexts (apply-reduction-relation red t))
      (for ([next (in-list (remove-duplicates nexts))])
        (cond
          [(equal? next to)
           (hash-set! parents to t)
           (done)]
          [(hash-ref parents next #f)
           (void)]
          [else
           (hash-set! parents next t)
           (loop next)]))))
  (let loop ([term to])
    (cond
      [(equal? term from) (list from)]
      [else (cons term (loop (hash-ref parents term)))])))

(define-metafunction coreLang
  isRestrictedByγ : ι τ RM γ -> boolean
  [(isRestrictedByγ ι τ RM (any_0 ... (ι τ vName) any_1 ...)) #t
   (side-condition (mo<=? (term acq) (term RM)))]
  [(isRestrictedByγ ι τ RM γ) #f])

(define-metafunction coreLang
  isPEntryInConflictWithα : (vName ι) α -> boolean
  [(isPEntryInConflictWithα (vName ι) α)
   ,(ormap (λ (x) (term (isPEntryInConflictWithPEntry (vName ι) ,x)))
           (term α))])

(define-metafunction coreLang
  isPEntryInConflictWithPEntry : (vName ι) postponedEntry -> boolean

  [(isPEntryInConflictWithPEntry (vName ι) (write vName   ι       WM  μ-value  )) #f]
  [(isPEntryInConflictWithPEntry (vName ι) (write vName_1 vName_2 WM  μ        )) #t]
  [(isPEntryInConflictWithPEntry (vName ι) (write vName_1 ι-var   rel μ        )) #t]
  [(isPEntryInConflictWithPEntry (vName ι) (write vName_1 ι_0     rlx μ        )) #f]

  [(isPEntryInConflictWithPEntry (vName ι) (read  vName_1 ι           any ...  )) #t]
  [(isPEntryInConflictWithPEntry (vName ι) (read  vName_1 vName_2     any ...  )) #t]
  [(isPEntryInConflictWithPEntry (vName ι) (read  vName_1 ι-var   acq any ...  )) #t]
  [(isPEntryInConflictWithPEntry (vName ι) (read  vName_1 ι_0         any ...  )) #f]

  [(isPEntryInConflictWithPEntry (vName ι) (let-in vName_1            any ...  )) #f]
  
  [(isPEntryInConflictWithPEntry (vName ι) (if vName_1 Expr α_0 α_1))
   (isPEntryInConflictWithα (vName ι) (appendT α_0 α_1))])

(define-metafunction coreLang
  isPEntryInConflictWithEifα : (vName ι) Eifα -> boolean
  [(isPEntryInConflictWithEifα (vName ι) hole) #f]
  [(isPEntryInConflictWithEifα (vName ι) (in-hole El (if vName_1 Expr Eifα α)))
   ,(and (term (isPEntryInConflictWithα    (vName ι) (elFirstPart El)))
         (term (isPEntryInConflictWithEifα (vName ι) Eifα)))]
  [(isPEntryInConflictWithEifα (vName ι) (in-hole El (if vName_1 Expr α Eifα)))
   ,(and (term (isPEntryInConflictWithα    (vName ι) (elFirstPart El)))
         (term (isPEntryInConflictWithEifα (vName ι) Eifα)))])

(define-metafunction coreLang
  canPostponedReadBePerformed : (vName ι-var RM σ-dd) σ α ifContext γ τ -> boolean
  
  ;; Can't resolve read from not yet resolved location.
  [(canPostponedReadBePerformed (vName_0 vName_1 RM σ-dd) σ_read α ifContext γ τ) #f]

  [(canPostponedReadBePerformed (vName ι RM σ-dd) σ_read
                                (in-hole Eifα (in-hole El (read vName ι RM σ-dd)))
                                ifContext γ τ)
   ,(and (not (term (isRestrictedByγ ι τ RM γ)))
         (equal? (term ifContext) (term ifContext_check))
         (not (term (isPEntryInConflictWithEifα (vName ι) Eifα)))
         (not (term (isPEntryInConflictWithα    (vName ι) (elFirstPart El))))
         (term (correctτ τ ι σ_to-check)))

   (where σ_to-check      (frontMerge σ_read σ-dd))
   (where ifContext_check (getIfContext Eifα))])

(define-metafunction coreLang
  canPostponedWriteBePerformed : (vName ι) α -> boolean
  [(canPostponedWriteBePerformed (vName ι)
                                 (postponedEntry ... (write vName ι WM μ-value) any ...))
   #t
   (side-condition (not (term (isPEntryInConflictWithα (vName ι) (postponedEntry ...)))))]

  [(canPostponedWriteBePerformed (vName ι) α) #f])

(define-metafunction coreLang
  elFirstPart : El -> (any ...)
  [(elFirstPart hole) ()]
  [(elFirstPart (any_0 ... hole any_1 ...)) (any_0 ...)])

;; (define (find-path red from to)
;;   (define parents (make-hash))
;;   (let/ec done
;;     (let loop ([t from])
;;       (define nexts (apply-reduction-relation red t))
;;       (for ([next (in-list (remove-duplicates nexts))])
;;         (cond
;;           [(equal? next to)
;;            (hash-set! parents to t)
;;            (done)]
;;           [(hash-ref parents next #f)
;;            (void)]
;;           [else
;;            (hash-set! parents next t)
;;            (loop next)]))))
;;   parents)

;; (define (getChildren from parents)
;;   (for/hash ([(k v) (in-hash parents)]
;;              #:unless (equal? k from))
;;     (values v k)))

;; (define (show-restricted-trace tracesF step from to)
;;   (define parents  (find-path step from to))
;;   (define children (getChildren from parents))
;;   (tracesF step from
;;           #:reduce
;;           (λ (_ t)
;;             (let/ec k
;;               (list
;;                (list #f
;;                      (hash-ref children t
;;                                (λ () (k '()))
;;                                )))))))

;; (define (show-restricted-trace-pp tracesF pp step from to)
;;   (define parents  (find-path step from to))
;;   (define children (getChildren from parents))
;;   (tracesF step from
;;           #:reduce
;;           (λ (_ t)
;;             (let/ec k
;;               (list (list #f (hash-ref children t (λ () (k '())))))))
;;           #:pp pp))
