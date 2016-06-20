#lang racket
(require redex/reduction-semantics)
(require graph)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-postponedReadRules) 

(define-metafunction coreLang
  getWriteToPropagate_α : ι α -> Maybe ;postponedEntry
  [(getWriteToPropagate_α ι ()) None]
  [(getWriteToPropagate_α ι ((read  vName ι-var acq σ-dd) any ...)) None]
  [(getWriteToPropagate_α ι ((read  vName ι     RM  σ-dd) any ...)) None]

  [(getWriteToPropagate_α ι ((write vName ι     WM  μ-value) any ...)) (Just (write vName ι WM μ-value))]
  [(getWriteToPropagate_α ι ((write vName ι     WM  μ      ) any ...)) None]

  [(getWriteToPropagate_α ι ((if vName Expr α_0 α_1) any ...)) None]

  [(getWriteToPropagate_α ι (any_0 any ...)) (getWriteToPropagate_α ι (any ...))])

(define-metafunction coreLang
  getWriteToPropagate : ι Eifα -> Maybe ;postponedEntry
  [(getWriteToPropagate ι hole) None]
  [(getWriteToPropagate ι (postponedEntry ... (if vName Expr Eifα α) any ...))
   ,(if (equal? (term Maybe) 'None)
        (term (getWriteToPropagate_α ι ,(reverse (term (postponedEntry ...)))))
        (term Maybe))
   (where Maybe (getWriteToPropagate ι Eifα))]
  [(getWriteToPropagate ι (postponedEntry ... (if vName Expr α Eifα) any ...))
   ,(if (equal? (term Maybe) 'None)
        (term (getWriteToPropagate_α ι ,(reverse (term (postponedEntry ...)))))
        (term Maybe))
   (where Maybe (getWriteToPropagate ι Eifα))]
)

(define-metafunction coreLang
  listToEdges : (any ...) -> ((any any) ...)
  [(listToEdges ()   ) ()]
  [(listToEdges (any)) ()]
  [(listToEdges (any_0 any_1)) ((any_0 any_1))]
  [(listToEdges (any_0 any_1 any_2 ...))
   (consT (any_0 any_1)
          (listToEdges (any_1 any_2 ...)))])

(define-metafunction coreLang
  observedWritesToEdges : ι observedWrites -> ((vName vName) ...)
  [(observedWritesToEdges ι (par observedWrites_0 observedWrites_1))
   (appendT (observedWritesToEdges ι observedWrites_0)
            (observedWritesToEdges ι observedWrites_1))]

  [(observedWritesToEdges ι (observedWriteLbl ...))
   (listToEdges (vName ...))
   (where observedWrites_ι
          ,(filter (λ (x) (match x
                            [(list vname loc)
                             (equal? loc (term ι))]))
                   (term (observedWriteLbl ...))))
   (where (vName ...)
          ,(map (λ (x) (match x [(list vname loc) vname]))
                (term observedWrites_ι)))])

(define-metafunction coreLang
  postponedEntryToWriteVNames : ι postponedEntry -> (vName ...)
  [(postponedEntryToWriteVNames ι (read   any ...)) ()]
  [(postponedEntryToWriteVNames ι (let-in any ...)) ()]
  [(postponedEntryToWriteVNames ι (write  vName ι   any ...)) (vName)]
  [(postponedEntryToWriteVNames ι (write  vName ι_0 any ...)) ()]
  [(postponedEntryToWriteVNames ι (if     vName Expr α_0 α_1))
   (appendT (αToWriteVNames ι α_0)
            (αToWriteVNames ι α_1))])

(define-metafunction coreLang
  αToWriteVNames : ι α -> (vName ...)
  [(αToWriteVNames ι α) ,(apply append
                                (map (λ (x) (term (postponedEntryToWriteVNames ι ,x)))
                                     (term α)))])

(define-metafunction coreLang
  αToEdges : ι α -> ((vName vName) ...)
  [(αToEdges ι α) (listToEdges (αToWriteVNames ι α))])

(define-metafunction coreLang
  φToEdges : ι φ -> ((vName vName) ...)
  [(φToEdges ι α) (αToEdges ι α)]
  [(φToEdges ι (par φ_0 φ_1)) (appendT (φToEdges ι φ_0)
                                       (φToEdges ι φ_1))])

(define-metafunction coreLang
  writesMOedges : ι φ observedWrites -> ((vName vName) ...)
  [(writesMOedges ι φ observedWrites)
   (appendT (φToEdges ι φ)
            (observedWritesToEdges ι observedWrites))])

(define (hasLoop edges)
  (ormap (λ (x) (> (length x) 1))
         (scc (unweighted-graph/directed edges))))

(define-metafunction coreLang
  hasιInObservedWrites : path ι auxξ -> boolean
  [(hasιInObservedWrites path ι auxξ) #t
   (where observedWrites           (getObservedWrites auxξ))
   (where (in-hole El (vName ι)) (getByPath path observedWrites))]

  [(hasιInObservedWrites path ι auxξ) #f])

(define-metafunction coreLang
  removeγRestrictionsByVName : vName γ -> γ
  [(removeγRestrictionsByVName vName γ)
   ,(filter (λ (x) (match x [(list loc t name)
                             (not (equal? name (term vName)))]))
            (term γ))])

(define-metafunction coreLang
  updateByFrontMod : RM path ι τ σ ψ -> ψ
  [(updateByFrontMod acq path ι τ σ ψ) (updateByFront path σ ψ)]
  [(updateByFrontMod RM  path ι τ σ ψ) (updateByFront path ((ι τ)) ψ)])

(define-metafunction coreLang
  getDataDependenciesMod : RM ι σ η -> σ-dd
  [(getDataDependenciesMod con ι σ η) (getDataDependencies ι σ η)]
  [(getDataDependenciesMod RM  ι σ η) ()])

(define-metafunction coreLang
  resolveObservedWrite_path : path observedWrites (vName ι τ) auxξ -> auxξ
  [(resolveObservedWrite_path path (par observedWrites_0 observedWrites_1) (vName ι τ) auxξ)
   auxξ_1
   (where auxξ_0 (resolveObservedWrite_path (updatePath L path) observedWrites_0 (vName ι τ) auxξ))
   (where auxξ_1 (resolveObservedWrite_path (updatePath R path) observedWrites_1 (vName ι τ) auxξ_0))]

  [(resolveObservedWrite_path path (in-hole El (vName ι)) (vName ι τ) auxξ)
   auxξ_upd_readψ
   
   (where observedWrites_old (getObservedWrites auxξ))
   (where observedWrites_new (updateOnPath path (elToList El) observedWrites_old))

   (where auxξ_upd_observedWrites (updateState (RW observedWrites_old)
                                               (RW observedWrites_new)
                                               auxξ))
   
   (where ψ_old (getReadψ auxξ))
   (where ψ_new (updateByFront path ((ι τ)) ψ_old))
   (where auxξ_upd_readψ          (updateState (Read ψ_old)
                                               (Read ψ_new)
                                               auxξ_upd_observedWrites))]

  [(resolveObservedWrite_path path observedWrites (vName ι τ) auxξ) auxξ])

(define-metafunction coreLang
  resolveObservedWrite : (vName ι τ) auxξ -> auxξ
  [(resolveObservedWrite (vName ι τ) auxξ)
   (resolveObservedWrite_path () (getObservedWrites auxξ) (vName ι τ) auxξ)])

;; TODO: Rewrite to tree traversal.
;; The current implementation doesn't work correctly
;; if a program contains a variable with name `choice`. 
(define (doesntContainChoice mu) ;; μ -> boolean
  (not (memv 'choice (flatten mu))))

(define-metafunction coreLang
  isSyncAction : postponedEntry -> boolean
  [(isSyncAction (read  vName ι-var acq σ-dd)) #t]
  [(isSyncAction (read  vName ι-var con σ-dd)) #t]
  [(isSyncAction (write vName ι-var rel μ   )) #t]
  [(isSyncAction (if vName Expr α_0 α_1))
   ,(or (term (existSyncAction α_0))
        (term (existSyncAction α_1)))]
  [(isSyncAction postponedEntry) #f])

(define-metafunction coreLang
  existSyncActions : α -> boolean
  [(existSyncActions α)
   ,(ormap (λ (x) (term (isSyncAction ,x))) (term α))])

(define-metafunction coreLang
  appendToα : Eif postponedEntry α -> α
  [(appendToα Eif1 postponedEntry α) (appendT α (postponedEntry))]

  [(appendToα (if vName Eif AST) postponedEntry (any_0 ... (if vName Expr α_0 α_1) any_1 ...))
   (any_0 ... (if vName Expr (appendToα Eif postponedEntry α_0) α_1) any_1 ...)]

  [(appendToα (if vName AST Eif) postponedEntry (any_0 ... (if vName Expr α_0 α_1) any_1 ...))
   (any_0 ... (if vName Expr α_0 (appendToα Eif postponedEntry α_1)) any_1 ...)])

(define-metafunction coreLang
  chooseBranch : number any any -> any
  [(chooseBranch 0      any_0 any_1) any_1]
  [(chooseBranch number any_0 any_1) any_0])

(define-metafunction coreLang
  insertListInEl : El (any ...) -> (any ...)
  [(insertListInEl (any_0 ... hole any_1 ...) any) (appendT (any_0 ...) (appendT any (any_1 ...)))])

(define (interleavings xs ys)
  (match (list xs ys)
    [(list (cons x xs) (cons y ys))
     (append (map (λ (zs) (cons x zs))
                  (interleavings xs (cons y ys)))
             (map (λ (zs) (cons y zs))
                  (interleavings (cons x xs) ys)))]

    [(list '() ys) (list ys)]
    [(list xs '()) (list xs)]))

(define-syntax-rule (define-postponedReadRules lang defaultState getWriteσ)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (in-hole Eif (read RM ι-var))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret  a       ))) auxξ_new))
        "read-postponed"
        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))
        
        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (read a ι-var RM ()) α))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM))))
        (side-condition (term (isPossibleEEif E Eif auxξ))))

   (-->  ((in-hole E (in-hole Eif (readCon RM ι-var σ-dd))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret          a       ))) auxξ_new))
        "readCon-postponed"
        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))

        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (read a ι-var RM σ-dd) α))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM))))
        (side-condition (term (isPossibleEEif E Eif auxξ))))
   
   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-resolve"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        
        (where (in-hole Ep α_thread) (getφ auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (where (in-hole El_0 (read vName ι RM σ-dd)) α)
        (where (in-hole El_1 (τ μ-value σ)) (getCellHistory ι η))
        (where path (pathEp Ep))

        (where ψ_read_new (updateByFrontMod RM path ι τ σ ψ_read))
        (where auxξ_upd_ψ (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ-dd_new   (frontMerge σ-dd (getDataDependenciesMod RM ι σ η)))

        (where α_new      (substμα vName μ-value σ-dd_new (elToList El_0)))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ_upd_ψ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_new   (updateState (R γ) (R γ_new) auxξ_upd_φ))

        (where σ_read     (getByPath path ψ_read))
        (where σ_to-check (frontMerge σ_read σ-dd))
        (where τ_read-min (fromMaybe 0 (lookup ι σ_to-check)))
        
        ;; TODO: add it to `canPostponedReadBePerformed`
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        
        (where ifContext (getIfContext Eifα))
        (side-condition (term
                         (canPostponedReadBePerformed (vName ι RM σ-dd) σ_read α_thread ifContext γ τ)))
      
        (side-condition (term (isPossibleRead path vName ι τ_read-min τ ifContext auxξ))))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-resolve-speculative"
        (where φ      (getφ auxξ))
        
        (where (in-hole Ep α_thread) φ)
        (where (in-hole Eifα α) α_thread)
        (where (in-hole El_reader (read vName ι rlx σ-dd)) α)
        
        (where (in-hole Ep_writer α_write) φ)
        (where (in-hole El_writer (write vName_1 ι rlx μ-value)) α_write)
        ;; (side-condition (term (canPostponedWriteBePerformed (vName_1 ι) α_write)))

        (where path (pathEp Ep))
        (where path_writer (pathEp Ep_writer))
        (side-condition (not (equal? (term path) (term path_writer))))

        (side-condition (not (term (existSyncActions (elFirstPart El_reader))))) ;; TODO: add to `canPostponedReadBePerformed`.
        (side-condition (not (term (existSyncActions (elFirstPart El_writer)))))

        (where ifContext (getIfContext Eifα))
        (side-condition (term (canPostponedReadBePerformedWOτ (vName ι rlx σ-dd) α_thread ifContext)))

        (where σ-dd_new  σ-dd) 
        (where α_new      (substμα vName μ-value σ-dd_new
                                   (elToList El_reader)))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_upd_γ (updateState (R γ) (R γ_new) auxξ_upd_φ))

        (where observedWrites       (getObservedWrites auxξ))
        (where observedWrites_check (snocOnPath path (vName_1 ι) observedWrites))

        (side-condition (not (hasLoop (term (writesMOedges ι φ observedWrites_check)))))

        (where observedWrites_new (snocOnPathIfNew path (vName_1 ι) observedWrites))
        (where auxξ_new           (updateState (RW observedWrites)
                                               (RW observedWrites_new)
                                               auxξ_upd_γ)))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-propagate"
        (where φ      (getφ auxξ))
        
        (where (in-hole Ep α_thread) φ)
        (where (in-hole Eifα α) α_thread)
        (where (in-hole El_reader (read vName ι rlx σ-dd)) α)
       
        (where Maybe (getWriteToPropagate_α ι ,(reverse (term (elFirstPart El_reader)))))
        (where (Just (write vName_1 ι WM μ-value))
               ,(if (equal? (term Maybe) 'None)
                    (term (getWriteToPropagate ι Eifα))
                    (term Maybe)))

        (where path (pathEp Ep))

        (where ifContext (getIfContext Eifα))
        ;; (side-condition (term (canPostponedReadBePerformedWOτ (vName ι rlx σ-dd) α_thread ifContext)))

        (where σ-dd_new  σ-dd) 
        (where α_new      (substμα vName μ-value σ-dd_new
                                   (elToList El_reader)))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_upd_γ (updateState (R γ) (R γ_new) auxξ_upd_φ))
        (where auxξ_new   auxξ_upd_γ)

        ;; (where observedWrites       (getObservedWrites auxξ))
        ;; (where observedWrites_check (snocOnPath path (vName_1 ι) observedWrites))

        ;; (side-condition (not (hasLoop (term (writesMOedges ι φ observedWrites_check)))))

        ;; (where observedWrites_new (snocOnPathIfNew path (vName_1 ι) observedWrites))
        ;; (where auxξ_new           (updateState (RW observedWrites)
                                               ;; (RW observedWrites_new)
                                               ;; auxξ_upd_γ))
        )

   ;; TODO: update the rule to the speculative reads
   (--> (AST auxξ)
        (stuck defaultState)
        "read-resolve-stuck"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El (read vName ι RM σ-dd)) α)
        (side-condition (not (term (isPEntryInConflictWithα (read vName ι) (elFirstPart El)))))
        
        (side-condition (term (isLocationUninitialized ι σ-dd (pathEp Ep) auxξ))))

   (-->  ((in-hole E (in-hole Eif ((ret μ) >>= (λ vName AST)))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (subst vName a AST)))         auxξ_new))
        ;; The substitution is needed to avoid collapse with previous
        ;; postponed operations.
        ">>=-subst-postpone"
        (side-condition (term (isPossibleEEif E Eif auxξ)))
        
        (where μ_simplified (calcμ μ))

        ;; μ can't be substituted immediately
        (side-condition (not (redex-match coreLang μ-subst (term μ_simplified))))

        ;; μ doesnt contain `choice` operator --- they should be resolved before
        ;; postponing.
        (side-condition (doesntContainChoice (term μ_simplified)))

        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))

        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (let-in a μ_simplified) α))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ)))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value AST) auxξ_new))
        ">>=-subst-resolve"

        (where (in-hole Ep α_thread) (getφ auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (where (in-hole El (let-in vName μ-value)) α)
        (where path (pathEp Ep))

        (where α_new    (substμα vName μ-value () (elToList El)))
        (where φ        (getφ auxξ))
        (where φ_new    (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))
        
        (where ifContext (getIfContext Eifα))
        (side-condition (term (isPossiblePath_resolve (vName ifContext) path auxξ))))

   (-->  ((in-hole E (in-hole Eif (write rlx ι-var μ))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret a            ))) auxξ_new))
        "write-rlx-postpone"
        (side-condition (if (equal? (term Eif) (term hole))
                            (term (isPossibleE E auxξ))
                            (term (isPossibleEEif E Eif auxξ))))
        
        (where μ_simplified (calcμ μ))

        ;; μ doesnt contain `choice` operator --- they should be resolved before
        ;; postponing.
        (side-condition (doesntContainChoice (term μ_simplified)))

        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))

        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (write a ι-var rlx μ_simplified) α))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ)))

   (-->  (AST  auxξ)
        (normalize 
         ((subst vName μ-value AST) auxξ_new))
        "write-resolve"

        (where (in-hole Ep α_thread) (getφ auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (side-condition (equal? (term Eifα) (term hole)))

        (where (in-hole El (write vName ι WM μ-value)) α)
        (side-condition (term
                         (canPostponedWriteBePerformed (vName ι) α)))

        (where path (pathEp Ep))

        ;; TODO: add to the `canPostponedWriteBePerformed`
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        
        (where ifContext (getIfContext Eifα))
        (side-condition (term (isPossiblePath_resolve (vName ifContext) path auxξ)))

        (where α_new      (substμα vName μ-value () (elToList El)))
        (where φ          (getφ auxξ))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ))

        (where η       (getη auxξ))
        (where ψ_read  (getReadψ auxξ))

        (where τ              (getNextTimestamp ι η))
        (where ψ_read_new     (updateByFront path ((ι τ)) ψ_read))                     ;; TODO: now it works only for relaxed writes.
        (where auxξ_upd_front (updateState (Read ψ_read) (Read ψ_read_new) auxξ_upd_φ))

        (where σ_write    (getWriteσ path auxξ))
        (where σ_ToWrite  (updateFront ι τ (getσToWrite σ_write ι η)))
        (where η_new      (updateCell  ι μ-value σ_ToWrite η))
        (where auxξ_upd_η (updateState η η_new auxξ_upd_front))
        (where auxξ_upd_γ (dupRelWriteRestrictions ι τ σ_write auxξ_upd_η))
        
        (where auxξ_upd_observedWrites (resolveObservedWrite (vName ι τ) auxξ_upd_γ))
        (where auxξ_new   auxξ_upd_observedWrites))

   (-->  ((in-hole E (in-hole Eif (if vName AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (chooseBranch number AST_0 AST_1))) auxξ_new))
        "if-speculation-branch-choice"
        
        ;; TODO: check if it's possible to move here.
        (where ifContext (eifToIfContext Eif))
        (side-condition (term (isPossiblePath_resolve (vName ifContext) (pathE E) auxξ)))

        (where φ (getφ auxξ))
        (where (in-hole Ep α_thread) φ)
        (where (in-hole Eifα (in-hole El (if vName number α_0 α_1))) α_thread)

        (where α_new (insertListInEl El (chooseBranch number α_0 α_1)))
        (where path (pathE E))
        (where φ_new (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ)))
  
   (-->  ((in-hole E (in-hole Eif (if Expr AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (if a    AST_0 AST_1))) auxξ_new))
        "if-speculation-init"
        
        (side-condition (term (isPossibleEEif E Eif auxξ))) ;; TODO: check if it's possible to move here.
        (where Expr_simplified (calc Expr))
        (side-condition (not (redex-match coreLang number (term Expr_simplified))))

        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))
        (side-condition (not (term (isIfInα Expr_simplified α))))

        (fresh a)
        (where α_new    (appendToα Eif (if a Expr_simplified () ()) α))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ)))
   
   (-->  (AST auxξ)
        (normalize
         ((subst vName_2 a (subst vName_1 a AST)) auxξ_new))
        "if-speculation-write-promoting"

        (where (in-hole Ep α_thread) (getφ auxξ))
        (where (in-hole Eifα α) α_thread)
        
        (where (in-hole El_0 (if vName_0 Expr α_1 α_2)) α)
        (where (in-hole El_1 (write vName_1 ι WM μ-value)) α_1)
        (where (in-hole El_2 (write vName_2 ι WM μ-value)) α_2)

        (side-condition (term
                         (canPostponedWriteBePerformed (vName_1 ι) α_1))) ;; TODO: check if it's possible to move here.
        (side-condition (term
                         (canPostponedWriteBePerformed (vName_2 ι) α_2)))

        (where path     (pathEp Ep))
        (side-condition (term (isPossiblePath path auxξ)))

        (fresh a)
        (where α_1_new (substμα vName_1 a () (elToList El_1)))
        (where α_2_new (substμα vName_2 a () (elToList El_2)))

        (where α_new (insertListInEl El_0
                      ((write a ι WM μ-value)
                       (if vName_0 Expr α_1_new α_2_new))))

        (where φ          (getφ auxξ))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_new   (updateState (P φ) (P φ_new) auxξ))
        )

   ;; Leads to very poor performance, but solves an issue with tests from etaPsi2SCpostLangTests.rkt
   ;; (-->  ((in-hole E (par (ret μ_0) (ret μ_1)))              auxξ)
   ;;      (normalize 
   ;;       ((in-hole E (ret (    μ_0       μ_1))) (joinST-2ψ path auxξ_new)))
   ;;      "join-postponed-operations-interleaving"
   ;;      (where path (pathE E))

   ;;      (where φ             (getφ auxξ))
   ;;      (where (par α_0 α_1) (getByPath path φ))
   ;;      (where (in-hole El α_interleaved) ,(interleavings (term α_0) (term α_1)))
   ;;      (where φ_new         (updateOnPath path α_interleaved φ))
   ;;      (where auxξ_upd_φ    (updateState (P φ) (P φ_new) auxξ))
        
   ;;      (where observedWrites (getObservedWrites auxξ))
   ;;      (where (par observedWrites_0 observedWrites_1)  (getByPath path observedWrites))
   ;;      (side-condition (and (equal? '() (term observedWrites_0))
   ;;                           (equal? '() (term observedWrites_1))))

   ;;      ;; TODO: weaken the previous side-condition
   ;;      ;; (where (in-hole El observedWrites_interleaved) ,(interleavings (term observedWrites_0)
   ;;      ;;                                                                (term observedWrites_1)))
   ;;      ;; (where observedWrites_new (updateOnPath path observedWrites_interleaved observedWrites))

   ;;      (where observedWrites_new (updateOnPath path () observedWrites))
   ;;      (where auxξ_new (updateState (RW observedWrites)
   ;;                                   (RW observedWrites_new)
   ;;                                   auxξ_upd_φ))

   ;;      (side-condition (term (isPossibleE E auxξ))))
)))
