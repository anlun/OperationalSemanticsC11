#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(provide (all-defined-out))

(define-metafunction coreLang
  getη : auxξ -> η
  [(getη (any_0 ... η any_1 ...)) η])

(define-metafunction coreLang
  getObservedWrites : auxξ -> observedWrites
  [(getObservedWrites (any_0 ... (RW observedWrites) any_1 ...)) observedWrites])

(define-metafunction coreLang
  updateState : any any auxξ -> auxξ
  [(updateState any_old any_new (any_0 ... any_old any_1 ...)) (any_0 ... any_new any_1 ...)])

(define-metafunction coreLang
  holeIndex : El -> number
  [(holeIndex (any_0 ... hole any_1 ...)) ,(length (term (any_0 ...)))])

(define-relation syntax
  correctτ ⊆ τ × ι × σ
  [(correctτ τ ι σ)
   ,(not (equal? (term None) (term (lookup ι σ))))     ; This condition check if location is mentioned in front.
   ,(>= (term τ) (term (fromMaybe -1 (lookup ι σ))))])

(define-metafunction coreLang
  getReadσ-tree  : auxξ -> σ-tree
  [(getReadσ-tree (any_0 ... (Read σ-tree) any_1 ...)) σ-tree])

(define-metafunction coreLang
  getAcqFront  : auxξ -> σ-tree
  [(getAcqFront (any_0 ... (AcqFront σ-tree) any_1 ...)) σ-tree])

(define-metafunction coreLang
  getRelFront  : auxξ -> χ-tree
  [(getRelFront (any_0 ... (RelFront χ-tree) any_1 ...)) χ-tree])

(define-metafunction coreLang
  getWriteσ-tree : auxξ -> σ-tree
  [(getWriteσ-tree (any_0 ... (Write σ-tree) any_1 ...)) σ-tree])

(define-metafunction coreLang
  getσSC : auxξ -> σ
  [(getσSC (any_0 ... (SC σ) any_1 ...)) σ])

(define-metafunction coreLang
  getσNA : auxξ -> σ
  [(getσNA (any_0 ... (NA σ) any_1 ...)) σ])

(define-metafunction coreLang
  getGR : auxξ -> G
  [(getGR (any_0 ... (Graph G) any_1 ...)) G])

(define-metafunction coreLang
  getGF : auxξ -> GF
  [(getGF (any_0 ... (GFront GF) any_1 ...)) GF])

#|
(define-metafunction coreLang
  updateStateF : any (any -> any) auxξ -> auxξ
  [(updateStateF any_old f (any_0 ... any_old any_1 ...)) (any_0 ... (f any_old) any_1 ...)])
|#

(define-metafunction coreLang
  dup : path any -> any
  [(dup ()            any         ) (par any any)]
  [(dup (L path) (par any_0 any_1)) (par (dup path any_0) any_1)]
  [(dup (R path) (par any_0 any_1)) (par any_0 (dup path any_1))])

(define-metafunction coreLang
  join : path σ-tree -> any
  [(join ()       (par σ_0 σ_1)) (frontMerge σ_0 σ_1)]
  [(join (L path) (par σ-tree_0 σ-tree_1)) (par (join path σ-tree_0) σ-tree_1)]
  [(join (R path) (par σ-tree_0 σ-tree_1)) (par σ-tree_0 (join path σ-tree_1))])

(define-metafunction coreLang
  [(getByPath () any) any]
  [(getByPath (L path) (par any_0 any_1)) (getByPath path any_0)]
  [(getByPath (R path) (par any_0 any_1)) (getByPath path any_1)])

(define-metafunction coreLang
  setFront : path σ σ-tree -> σ-tree
  [(setFront ()       σ_new σ)                       σ_new]
  [(setFront (L path) σ_new (par σ-tree_0 σ-tree_1)) (par (setFront path σ_new σ-tree_0) σ-tree_1)]
  [(setFront (R path) σ_new (par σ-tree_0 σ-tree_1)) (par σ-tree_0 (setFront path σ_new σ-tree_1))])

(define-metafunction coreLang
  updateByFront : path σ σ-tree -> σ-tree
  [(updateByFront ()       σ_delta            σ)  (frontMerge σ_delta σ)]
  [(updateByFront (L path) σ_delta (par σ-tree_0 σ-tree_1)) (par (updateByFront path σ_delta σ-tree_0) σ-tree_1)]
  [(updateByFront (R path) σ_delta (par σ-tree_0 σ-tree_1)) (par σ-tree_0 (updateByFront path σ_delta σ-tree_1))])

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
  [(getReadσ path auxξ) (getByPath path (getReadσ-tree auxξ))])

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
   (updateState (Read σ-tree) (Read σ-tree_new) auxξ)
   (where σ-tree     (getReadσ-tree auxξ))
   (where σ-tree_new (updateByFront path σ σ-tree))])

(define-metafunction coreLang
  getWriteσ : path auxξ -> σ
  [(getWriteσ path auxξ) (getByPath path σ-tree)
   (where (any_0 ... (Write σ-tree) any_1 ...) auxξ)]
  [(getWriteσ path auxξ) ()])

(define-metafunction coreLang
  synchronizeCurReleaseFronts : path auxξ -> auxξ
  [(synchronizeCurReleaseFronts path auxξ) (any_0 ... (RelFront χ-tree_new) any_1 ...)
   (where (any_0 ... (RelFront χ-tree) any_1 ...) auxξ)
   (where σ_cur (getByPath path (getReadσ-tree auxξ)))
   (where χ_new ,(map (λ (p) (list (car p) (term σ_cur)))
                      (term σ_cur)))
   (where χ-tree_new (updateOnPath path χ_new χ-tree))]
  [(synchronizeCurReleaseFronts path auxξ) auxξ])

(define-metafunction coreLang
  synchronizeWriteFront : path auxξ -> auxξ
  [(synchronizeWriteFront path auxξ)
   (updateState (Write σ-tree_write) (Write σ-tree_write_new) auxξ)
   (where (any_0 ... (Read σ-tree_read) any_1 ... (Write σ-tree_write) any_2 ...) auxξ)
   (where σ           (getByPath     path   σ-tree_read))
   (where σ-tree_write_new (updateByFront path σ σ-tree_write))]
  [(synchronizeWriteFront path auxξ) auxξ])

(define-metafunction coreLang
  spwST : path auxξ -> auxξ
  [(spwST path auxξ)
   (spwST-gr       path
   (spwST-α-tree        path
   (spwST-relFront path
   (spwST-acqFront path
   (spwST-writeσ-tree   path
   (spwST-readσ-tree    path auxξ))))))])

(define-metafunction coreLang
  spwST-readσ-tree : path auxξ -> auxξ
  [(spwST-readσ-tree path auxξ)
   (updateState (Read σ-tree) (Read (dup path σ-tree)) auxξ)
   (where (any_0 ... (Read σ-tree) any_1 ...) auxξ)]
  [(spwST-readσ-tree path auxξ) auxξ])

(define-metafunction coreLang
  spwST-writeσ-tree : path auxξ -> auxξ
  [(spwST-writeσ-tree path auxξ)
   (updateState (Write σ-tree) (Write (updateOnPath path (par () ()) σ-tree)) auxξ)
   (where (any_0 ... (Write σ-tree) any_1 ...) auxξ)]
  [(spwST-writeσ-tree path auxξ) auxξ])

(define-metafunction coreLang
  spwST-acqFront : path auxξ -> auxξ
  [(spwST-acqFront path auxξ)
   (updateState (AcqFront σ-tree) (AcqFront (updateOnPath path (par σ σ) σ-tree)) auxξ)
   (where (any_0 ... (AcqFront σ-tree) any_1 ...) auxξ)
   (where σ (getByPath path σ-tree))]
  [(spwST-acqFront path auxξ) auxξ])

(define-metafunction coreLang
  spwST-relFront : path auxξ -> auxξ
  [(spwST-relFront path auxξ)
   (updateState (RelFront χ-tree) (RelFront (updateOnPath path (par () ()) χ-tree)) auxξ)
   (where (any_0 ... (RelFront χ-tree) any_1 ...) auxξ)]
  [(spwST-relFront path auxξ) auxξ])

(define-metafunction coreLang
  spwST-α-tree : path auxξ -> auxξ
  [(spwST-α-tree path auxξ) auxξ_new
   (where (any_0 ... (P α-tree) any_1 ... (RW observedWrites) any_2 ...) auxξ)
   (where auxξ_α-tree   (updateState (P α-tree) (P (dup path α-tree)) auxξ))
   (where auxξ_new (updateState (RW observedWrites)
                                (RW (dup path observedWrites))
                                auxξ_α-tree))]
  [(spwST-α-tree path auxξ) auxξ])

(define-metafunction coreLang
  spwST-gr : path auxξ -> auxξ
  [(spwST-gr path auxξ) (updateState (Graph G) (Graph G_new)
                            (updateState (GFront GF) (GFront GF_new) auxξ))
                        
                         (where (any_0 ... (Graph G) any_1 ... (GFront GF) any_2 ...) auxξ)

                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_fork (number_new skip))
                         
                         (where number_old (getByPath path GF))
                         (where Edges_new ,(cons
                                            (term (number_old number_new sb))
                                            (term Edges)))
                         
                         (where Nodes_new ,(cons (term Node_fork) (term Nodes)))
                         (where G_new  (Nodes_new Edges_new))
                         (where GF_new (updateOnPath path (par number_new number_new) GF))]

  [(spwST-gr path auxξ) auxξ])

(define-metafunction coreLang
  joinST : path auxξ -> auxξ
  [(joinST path auxξ)
   (joinST-gr       path
   (joinST-α-tree        path
   (joinST-relFront path
   (joinST-acqFront path
   (joinST-writeσ-tree   path
   (joinST-readσ-tree    path auxξ))))))])

(define-metafunction coreLang
  joinST-readσ-tree : path auxξ -> auxξ
  [(joinST-readσ-tree path auxξ)
   (updateState (Read σ-tree) (Read (join path σ-tree)) auxξ)
   (where (any_0 ... (Read σ-tree) any_1 ...) auxξ)]
  [(joinST-readσ-tree path auxξ) auxξ])

(define-metafunction coreLang
  joinST-writeσ-tree : path auxξ -> auxξ
  [(joinST-writeσ-tree path auxξ)
   (updateState (Write σ-tree) (Write (updateOnPath path () σ-tree)) auxξ)
   (where (any_0 ... (Write σ-tree) any_1 ...) auxξ)]
  [(joinST-writeσ-tree path auxξ) auxξ])

(define-metafunction coreLang
  joinST-acqFront : path auxξ -> auxξ
  [(joinST-acqFront path auxξ)
   (updateState (AcqFront σ-tree) (AcqFront (join path σ-tree)) auxξ)
   (where (any_0 ... (AcqFront σ-tree) any_1 ...) auxξ)]
  [(joinST-acqFront path auxξ) auxξ])

(define-metafunction coreLang
  joinST-relFront : path auxξ -> auxξ
  [(joinST-relFront path auxξ)
   (updateState (RelFront χ-tree) (RelFront (updateOnPath path () χ-tree)) auxξ)
   (where (any_0 ... (RelFront χ-tree) any_1 ...) auxξ)]
  [(joinST-relFront path auxξ) auxξ])

(define-metafunction coreLang
  joinST-α-tree : path auxξ -> auxξ
  [(joinST-α-tree path auxξ) auxξ_new
   (where (any_0 ... (P α-tree) any_1 ... (RW observedWrites) any_2 ...) auxξ)
   (where auxξ_α-tree (updateState (P α-tree) (P (updateOnPath path () α-tree)) auxξ))
   
   (where (par observedWrites_0 observedWrites_1) (getByPath path observedWrites))
   (where observedWrites_new (updateOnPath path ((par observedWrites_0 observedWrites_1))
                                           observedWrites))

   (where auxξ_new (updateState (RW observedWrites) (RW observedWrites_new) auxξ_α-tree))]
  [(joinST-α-tree path auxξ) auxξ])

(define-metafunction coreLang
  joinST-gr : path auxξ -> auxξ
  [(joinST-gr path auxξ) (updateState (Graph G) (Graph G_new)
                             (updateState (GFront GF) (GFront GF_new) auxξ))
                         
                         (where (any_0 ... (Graph G) any_1 ... (GFront GF) any_2 ...) auxξ)
                         (where (Nodes Edges) G)
                         (where number_new ,(getNextNodeNumber (term Nodes)))
                         (where Node_join (number_new skip))
                         
                         (where (par number_left number_right) (getByPath path GF))
                         
                         (where Nodes_new ,(cons (term Node_join) (term Nodes)))
                         (where Edges_new ,(append
                                            (term
                                             ((number_left  number_new sb)
                                              (number_right number_new sb)))
                                            (term Edges)))
                         (where G_new (Nodes_new Edges_new))
                         
                         (where GF_new (updateOnPath path number_new GF))]
  [(joinST-gr path auxξ) auxξ])

;; Postponed reads part

(define-metafunction coreLang
  getα-tree : auxξ -> α-tree
  [(getα-tree (any_0 ... (P α-tree) any_1 ...)) α-tree])

(define-metafunction coreLang
  getγ : auxξ -> γ
  [(getγ (any_0 ... (R γ) any_1 ...)) γ])

(define-metafunction coreLang
  pathEp : Ep -> path
  [(pathEp hole) ()]
  [(pathEp (par Ep α-tree)) (L (pathEp Ep))]
  [(pathEp (par α-tree Ep)) (R (pathEp Ep))])

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
  addWriteNode : Action path auxξ -> auxξ
  [(addWriteNode (write WM ι μ-value τ) path auxξ)
                 (updateState (Graph G) (Graph G_new)
                     (updateState (GFront GF) (GFront GF_new) auxξ))
                     (where (any_0 ... (Graph G) any_1 ... (GFront GF) any_2 ...) auxξ)
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
                     (where GF_new (updateOnPath path number_new GF))]
  [(addWriteNode Action path auxξ) auxξ])

(define-metafunction coreLang
  is-α-== : α-tree path auxξ -> boolean
  [(is-α-== α-tree path auxξ) ,(equal? (term α-tree) (term α-tree_path))
                              (where (any_0 ... (P α-tree_all) any_1 ...) auxξ)
                              (where α-tree_path (getByPath path α-tree_all))]
  [(is-α-== α-tree path auxξ) #t])

(define-metafunction coreLang
  is-α-empty : path auxξ -> boolean
  [(is-α-empty path auxξ) (is-α-== () path auxξ)])

(define-metafunction coreLang
  isPostRlx : postponedEntry -> boolean
  [(isPostRlx (read   vName ι-var rlx σ-dd)) #t]
  [(isPostRlx (read   vName ι-var con σ-dd)) #t]
  [(isPostRlx (let-in vName μ))              #t]
  [(isPostRlx (write  vName ι-var rlx μ   )) #t]
  [(isPostRlx (if vName μ α_0 α_1))
   ,(and (term (are∀PostRlxInα α_0))
         (term (are∀PostRlxInα α_1)))]
  [(isPostRlx any)                           #f])

(define-metafunction coreLang
  are∀PostRlxInα : α -> boolean
  [(are∀PostRlxInα α) ,(andmap (λ (x) (term (isPostRlx ,x))) (term α))])

;; TODO: rename appropriately
(define-metafunction coreLang
  are∀PostReadsRlx : path auxξ -> boolean
  [(are∀PostReadsRlx path (any_0 ... (P α-tree_all) any_1 ...)) (are∀PostRlxInα α)
                                                       (where α (getByPath path α-tree_all))]
  [(are∀PostReadsRlx path auxξ) #t])

(define-metafunction coreLang
  ιNotInPostponedEntry : ι postponedEntry -> boolean
  [(ιNotInPostponedEntry ι (read  vName         ι RM σ-dd)) #f]
  [(ιNotInPostponedEntry ι (read  vName_0 vName_1 RM σ-dd)) #f]
  [(ιNotInPostponedEntry ι (write vName   ι       WM μ   )) #f]
  [(ιNotInPostponedEntry ι (write vName_0 vName_1 WM μ   )) #f]

  [(ιNotInPostponedEntry ι (if vName μ α_0 α_1))
   ,(and (term (ι-not-in-α ι α_0))
         (term (ι-not-in-α ι α_1)))]

  [(ιNotInPostponedEntry ι postponedEntry)                  #t])

(define-metafunction coreLang
  ι-not-in-α : ι α -> boolean
  [(ι-not-in-α ι α) ,(andmap (λ (x) (term (ιNotInPostponedEntry ι ,x))) (term α))])
   
(define-metafunction coreLang
  ι-not-in-α-tree : ι path auxξ -> boolean
  [(ι-not-in-α-tree ι path (any_0 ... (P α-tree) any_1 ...))
                                 (ι-not-in-α ι α)
                                 (where α (getByPath path α-tree))]
  [(ι-not-in-α-tree ι path auxξ) #t])

(define-metafunction coreLang
  αToγRecords : ι τ α -> γ
  [(αToγRecords ι τ α) ,(apply
                         append (map
                                 (λ (x) (match x [(list 'read vName locvar mod ddFront)
                                                  (list (list (term ι) (term τ) vName))]
                                                 [(list 'write vName locvar mod mu)
                                                  (list (list (term ι) (term τ) vName))]
                                                 [_ (list)]))
                                 (term α)))])

(define-metafunction coreLang
  flat-ObservedWrites : observedWrites -> ((vName ι) ...)
  [(flat-ObservedWrites observedWriteList) (flat-ObservedWriteList observedWriteList)]
  [(flat-ObservedWrites (par observedWrites_0 observedWrites_1))
                        (appendT (flat-ObservedWrites observedWrites_0)
                                 (flat-ObservedWrites observedWrites_1))])

(define-metafunction coreLang
  flat-ObservedWrites-ι : ι observedWrites -> ((vName ι) ...)
  [(flat-ObservedWrites-ι ι observedWrites)
   ,(filter (λ (x) (equal? (cadr x) (term ι))) (term (flat-ObservedWrites observedWrites)))])

(define-metafunction coreLang
  flat-ObservedWriteList : observedWriteList -> ((vName ι) ...)
  [(flat-ObservedWriteList observedWriteList)
   ,(apply append
           (map (λ (x) (match x
                         [(list name loc) (list x)]
                         [(list 'par list0 list1)
                          (append (term (flat-ObservedWrites ,list0))
                                  (term (flat-ObservedWrites ,list1)))]))
                (term observedWriteList)))])

(define-metafunction coreLang
  flattenObservedWriteList : path observedWrites -> ((vName ι) ...)
  [(flattenObservedWriteList path observedWrites)
   (flat-ObservedWriteList (getByPath path observedWrites))])

(define-metafunction coreLang
  addObservedWritesToγ : path ι τ WM auxξ -> auxξ
  [(addObservedWritesToγ path ι τ rlx auxξ) auxξ]
  [(addObservedWritesToγ path ι τ WM (any_0 ... (R γ) any_1 ... (RW observedWrites) any_2 ...))
   (any_0 ... (R γ_new) any_1 ... (RW observedWrites) any_2 ...)
   (where γ_new ,(append (map (λ (x) (match x [(list name loc)
                                               (list (term ι) (term τ) name)]))
                              (term (flattenObservedWriteList path observedWrites)))
                         (term γ)))]

  [(addObservedWritesToγ path ι τ WM auxξ) auxξ])

;; TODO: rename appropriately
(define-metafunction coreLang
  addPostReadsToγ : path ι τ auxξ -> auxξ
  [(addPostReadsToγ path ι τ (any_0 ... (P α-tree) any_1 ... (R γ) any_2 ...))
   (any_0 ... (P α-tree) any_1 ... (R γ_new) any_2 ...)
   (where α (getByPath path α-tree))
   (where γ_new ,(append (term (αToγRecords ι τ α)) (term γ)))]
  [(addPostReadsToγ path ι τ auxξ) auxξ])

(define-metafunction coreLang
  addPostReadsToγ_α : α ι τ auxξ -> auxξ
  [(addPostReadsToγ_α α ι τ (any_0 ... (P α-tree) any_1 ... (R γ) any_2 ...))
   (any_0 ... (P α-tree) any_1 ... (R γ_new) any_2 ...)
   (where γ_new ,(append (term (αToγRecords ι τ α)) (term γ)))]
  [(addPostReadsToγ_α α ι τ auxξ) auxξ])

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
  getσReleaseToWrite : ι χ -> σ
  [(getσReleaseToWrite ι χ) σ
   (where (Just σ) (lookup ι χ))]
  [(getσReleaseToWrite ι χ) ()])

(define-metafunction coreLang
  getσToWrite : σ ι η -> σ
  [(getσToWrite σ_write ι η) σ
                             (where (Just τ) (lookup ι σ_write))
                             (where (Just (μ-value σ)) (lookup3 τ (getCellHistory ι η)))]
  [(getσToWrite σ_write ι η) ()])

(define-metafunction coreLang
  updateχ : ι σ χ -> χ
  [(updateχ ι σ (any_0 ... (ι σ_old) any_1 ...)) (any_0 ... (ι σ) any_1 ...)]
  [(updateχ ι σ χ)                           (consT (ι σ) χ)])

(define-metafunction coreLang
  updateRelFront : path ι σ auxξ -> auxξ
  [(updateRelFront path ι σ (any_0 ... (RelFront χ-tree) any_1 ...)) (any_0 ... (RelFront χ-tree_new) any_1 ...)
   (where χ          (getByPath path χ-tree))
   (where χ-tree_new (updateOnPath path (updateχ ι σ χ) χ-tree))]
  [(updateRelFront path ι σ auxξ) auxξ])

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
  [(dupRelWriteRestrictions ι τ_rlx σ_write (any_0 ... (R γ) any_1 ...))
   (any_0 ... (R γ_new) any_1 ...)
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
  getLastFront : ι η -> σ
  [(getLastFront ι η)
   (fromMaybe () (getFrontByTimestamp ι τ_last η))
   (where τ_last (getLastTimestamp ι η))])

(define-metafunction coreLang
  acqFailCASσReadNew : ι η σ -> σ
  [(acqFailCASσReadNew ι η σ_read)
   (frontMerge σ_read (getLastFront ι η))])

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
  isRestrictedByγ_auxξ : ι τ RM auxξ -> boolean
  [(isRestrictedByγ_auxξ ι τ RM (any_0 ... (R γ) any_1 ...)) (isRestrictedByγ ι τ RM γ)]
  [(isRestrictedByγ_auxξ ι τ RM auxξ) #f])

(define-metafunction coreLang
  isPEntryInConflictWithα : (any vName ι) α -> boolean
  [(isPEntryInConflictWithα (any vName ι) α)
   ,(ormap (λ (x) (term (isPEntryInConflictWithPEntry (any vName ι) ,x)))
           (term α))])

(define-metafunction coreLang
  isPEntryInConflictWithPEntry : (any vName ι) postponedEntry -> boolean

  [(isPEntryInConflictWithPEntry (any vName ι) (write vName   ι       WM  μ-value  )) #f]
  [(isPEntryInConflictWithPEntry (any vName ι) (write vName_1 vName_2 WM  μ        )) #t]

  [(isPEntryInConflictWithPEntry (write vName ι) (write vName_1 ι_1       rel μ        ))
   ,(equal? (term ι) (term ι_1))]
  [(isPEntryInConflictWithPEntry (any vName ι) (write vName_1 ι-var   rel μ        )) #t]

  [(isPEntryInConflictWithPEntry (any vName ι) (write vName_1 ι_0     rlx μ        ))
   ,(equal? (term ι) (term ι_0))]

  [(isPEntryInConflictWithPEntry (any   vName ι) (read  vName_1 vName_2 RM  σ-dd)) #t]
  ;; [(isPEntryInConflictWithPEntry (write vName ι) (read  vName_1 ι-var   acq σ-dd))
  ;;  ,(equal? (term ι) (term ι-var))]
  [(isPEntryInConflictWithPEntry (any   vName ι) (read  vName_1 ι-var   acq σ-dd)) #t]
  [(isPEntryInConflictWithPEntry (any   vName ι) (read  vName_1 ι_0     RM  σ-dd))
   ,(equal? (term ι) (term ι_0))]

  [(isPEntryInConflictWithPEntry (any vName ι) (let-in vName_1         any_0 ...)) #f]
  
  [(isPEntryInConflictWithPEntry (any vName ι) (if vName_1 Expr α_0 α_1))
   (isPEntryInConflictWithα (any vName ι) (appendT α_0 α_1))])

(define-metafunction coreLang
  isPEntryInConflictWithEifα : (any vName ι) Eifα -> boolean
  [(isPEntryInConflictWithEifα (any vName ι) hole) #f]
  [(isPEntryInConflictWithEifα (any vName ι) (in-hole El (if vName_1 Expr Eifα α)))
   ,(and (term (isPEntryInConflictWithα    (any vName ι) (elFirstPart El)))
         (term (isPEntryInConflictWithEifα (any vName ι) Eifα)))]
  [(isPEntryInConflictWithEifα (any vName ι) (in-hole El (if vName_1 Expr α Eifα)))
   ,(and (term (isPEntryInConflictWithα    (any vName ι) (elFirstPart El)))
         (term (isPEntryInConflictWithEifα (any vName ι) Eifα)))])

(define-metafunction coreLang
  canPostponedReadBePerformed : (vName ι-var RM σ-dd) σ α ifContext γ τ -> boolean
  
  ;; Can't resolve read from not yet resolved location.
  [(canPostponedReadBePerformed (vName_0 vName_1 RM σ-dd) σ_read α ifContext γ τ) #f]

  [(canPostponedReadBePerformed (vName ι RM σ-dd) σ_read
                                (in-hole Eifα (in-hole El (read vName ι RM σ-dd)))
                                ifContext γ τ)
   ,(and (term (correctτ τ ι σ_to-check))
         (not (term (isRestrictedByγ ι τ RM γ)))
         (term (canPostponedReadBePerformedWOτ (vName ι RM σ-dd)
                                               (in-hole Eifα (in-hole El (read vName ι RM σ-dd)))
                                               ifContext)))

   (where σ_to-check      (frontMerge σ_read σ-dd))])

(define-metafunction coreLang
  canPostponedReadBePerformedWOτ : (vName ι-var RM σ-dd) α ifContext -> boolean
  
  ;; Can't resolve read from not yet resolved location.
  [(canPostponedReadBePerformedWOτ (vName_0 vName_1 RM σ-dd) α ifContext) #f]

  [(canPostponedReadBePerformedWOτ (vName ι RM σ-dd)
                                   (in-hole Eifα (in-hole El (read vName ι RM σ-dd)))
                                   ifContext)
   ,(and (equal? (term ifContext) (term ifContext_check))
         (not (term (isPEntryInConflictWithEifα (read vName ι) Eifα)))
         (not (term (isPEntryInConflictWithα    (read vName ι) (elFirstPart El)))))

   (where ifContext_check (getIfContext Eifα))])

(define-metafunction coreLang
  canPostponedWriteBePerformed : (vName ι) α -> boolean
  [(canPostponedWriteBePerformed (vName ι)
                                 (postponedEntry ... (write vName ι WM μ-value) any ...))
   #t
   (side-condition (not (term (isPEntryInConflictWithα (write vName ι) (postponedEntry ...)))))]

  [(canPostponedWriteBePerformed (vName ι) α) #f])

(define-metafunction coreLang
  elFirstPart : El -> (any ...)
  [(elFirstPart hole) ()]
  [(elFirstPart (any_0 ... hole any_1 ...)) (any_0 ...)])

(define-metafunction coreLang
  resolveWriteγ_η_el : vName σ (ι τ vName) η -> η 
  [(resolveWriteγ_η_el vName σ (ι τ vName) (any_0 ... (ι (any_1 ... (τ μ-value σ_rec) any_2 ...)) any_3 ...))
   (any_0 ... (ι (any_1 ... (τ μ-value (frontMerge σ σ_rec)) any_2 ...)) any_3 ...)]
   ;;                     (in-hole El_cell (ι (in-hole El_record (τ μ-value σ_rec))))) 
   ;; (in-hole El_cell (ι (in-hole El_record (τ μ-value (frontMerge σ σ_rec)))))]
  [(resolveWriteγ_η_el vName σ (ι τ vName_0) η) η])

(define-metafunction coreLang
  resolveWriteγ_σ-tree_el : path vName σ σ-tree -> σ-tree 
  [(resolveWriteγ_σ-tree_el path vName σ σ-tree) (updateByFront path σ σ-tree)])

(define-metafunction coreLang
  resolveWriteγ : path vName σ auxξ -> auxξ
  [(resolveWriteγ path vName σ auxξ) auxξ_new 
   (where γ (getγ auxξ))
   (where η (getη auxξ))
   (where η_new ,(foldl (λ (r eta)
                          (term (resolveWriteγ_η_el vName σ ,r ,eta)))
                        (term η) (term γ)))
   (where auxξ_upd_η   (updateState η η_new auxξ))
   (where σ-tree_write      (getWriteσ-tree auxξ_upd_η))
   (where σ-tree_write_new ,(if (equal? (term η) (term η_new))
                           (term σ-tree_write)
                           (term (updateByFront path σ σ-tree_write))))
   (where auxξ_new (updateState (Write σ-tree_write) (Write σ-tree_write_new) auxξ_upd_η))])

(define-metafunction coreLang
  hasιInObservedWrites : path ι auxξ -> boolean
  [(hasιInObservedWrites path ι (any_0 ... (RW observedWrites) any_1 ...)) #t
   (where (in-hole El (vName ι)) (flattenObservedWriteList path observedWrites))]

  [(hasιInObservedWrites path ι auxξ) #f])
 
(define-metafunction coreLang
  updateAcqFront : path σ auxξ -> auxξ
  [(updateAcqFront path σ (any_0 ... (AcqFront σ-tree) any_1 ...))
   (any_0 ... (AcqFront (updateByFront path σ σ-tree)) any_1 ...)]
  [(updateAcqFront path σ auxξ) auxξ])

(define-metafunction coreLang
  synchronizeCurAcqFronts : path auxξ -> auxξ
  [(synchronizeCurAcqFronts path auxξ) (updateState (Read σ-tree) (Read σ-tree_new) auxξ)
   (where (any_0 ... (Read σ-tree) any_1 ... (AcqFront σ-tree_acq) any_2 ...) auxξ)
   (where σ          (getByPath path σ-tree_acq))
   (where σ-tree_new (setFront path σ σ-tree))]
  [(synchronizeCurAcqFronts path auxξ) auxξ])

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
