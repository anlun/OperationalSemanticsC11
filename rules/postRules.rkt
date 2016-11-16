#lang racket
(require redex/reduction-semantics)
(require graph)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-postRules) 

(define-metafunction coreLang
  snocOnPathIfNew : path any any -> any
  [(snocOnPathIfNew () any_0 any_1)
   ,(if (member (term any_0) (term any_1))
        (term any_1)
        (term (snocT any_0 any_1)))]
  [(snocOnPathIfNew (L path) any_0 (par any_1 any_2))
   (par (snocOnPathIfNew path any_0 any_1) any_2)]
  [(snocOnPathIfNew (R path) any_0 (par any_1 any_2))
   (par any_1 (snocOnPathIfNew path any_0 any_2))])

(define-metafunction coreLang
  snocOnPath : path any any -> any
  [(snocOnPath () any_0 any_1) (snocT any_0 any_1)]
  [(snocOnPath (L path) any_0 (par any_1 any_2)) (par (snocOnPath path any_0 any_1) any_2)]
  [(snocOnPath (R path) any_0 (par any_1 any_2)) (par any_1 (snocOnPath path any_0 any_2))])

(define-metafunction coreLang
  isPostponedEntryIfIdentifier : any postponedEntry -> boolean
  [(isPostponedEntryIfIdentifier vName (if vName   any_1 ...)) #t]
  [(isPostponedEntryIfIdentifier vName (if vName_1 Expr α_0 α_1))
   ,(or (term (is-if-in-α vName α_0))
        (term (is-if-in-α vName α_1)))]
  [(isPostponedEntryIfIdentifier any_0 any_1               ) #f])

(define-metafunction coreLang
  ;; Checks if there is a postponed operation with the `any' identifier
  ;; (the first argument).
  is-if-in-α : any α -> boolean
  [(is-if-in-α any α) ,(ormap (λ (x)
                             (term (isPostponedEntryIfIdentifier any ,x)))
                           (term α))])

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
  list-to-edges : (any ...) -> ((any any) ...)
  [(list-to-edges ()   ) ()]
  [(list-to-edges (any)) ()]
  [(list-to-edges (any_0 any_1)) ((any_0 any_1))]
  [(list-to-edges (any_0 any_1 any_2 ...))
   (consT (any_0 any_1)
          (list-to-edges (any_1 any_2 ...)))])

(define-metafunction coreLang
  observedWriteList-to-edges_vName : vName ι observedWriteList -> ((vName vName) ...)
  [(observedWriteList-to-edges_vName vName ι observedWriteList)
   ,(map (λ (x) (match x [(list name loc) (list (term vName) name)]))
         (term observedWrites_ι))
   (where observedWrites_ι
          ,(filter (λ (x) (match x
                            [(list vname loc)
                             (equal? loc (term ι))]))
                   (term (flat-ObservedWriteList observedWriteList))))])

(define-metafunction coreLang
  observedWriteList-to-edges : ι observedWriteList -> ((vName vName) ...)
  [(observedWriteList-to-edges ι ()) ()]

  [(observedWriteList-to-edges ι ((vName ι) any ...))
   (appendT (observedWriteList-to-edges ι (any ...))
            (observedWriteList-to-edges_vName vName ι (any ...)))]

  [(observedWriteList-to-edges ι ((vName ι_0) any ...))
   (observedWriteList-to-edges ι (any ...))]

  [(observedWriteList-to-edges ι ((par observedWrites_0 observedWrites_1) any ...))
   ,(append (term (observedWriteList-to-edges ι (any ...)))
            (term (observedWrites-to-edges ι observedWrites_0))
            (term (observedWrites-to-edges ι observedWrites_1))
            (apply append
                   (map (λ (x) (term (observedWriteList-to-edges_vName ,(car x) ι (any ...))))
                        (term (flat-ObservedWrites-ι ι (par observedWrites_0 observedWrites_1))))))])

(define-metafunction coreLang
  observedWrites-to-edges : ι observedWrites -> ((vName vName) ...)
  [(observedWrites-to-edges ι (par observedWrites_0 observedWrites_1))
   (appendT (observedWrites-to-edges ι observedWrites_0)
            (observedWrites-to-edges ι observedWrites_1))]

  [(observedWrites-to-edges ι observedWriteList)
   (observedWriteList-to-edges ι observedWriteList)])

(define-metafunction coreLang
  isWriteTheOldest : vName ι auxξ -> boolean
  [(isWriteTheOldest vName ι auxξ)
   ,(not (ormap (λ (x) (match x [(list name0 name1)
                                 (and (equal? name1 (term vName))
                                      (not (equal? name0 name1)))]))
                (term (observedWrites-to-edges ι observedWrites))))
   (where observedWrites (getObservedWrites auxξ))])
   
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
  α-to-edges : ι α -> ((vName vName) ...)
  [(α-to-edges ι α) (list-to-edges (αToWriteVNames ι α))])

(define-metafunction coreLang
  α-tree-to-edges : ι α-tree -> ((vName vName) ...)
  [(α-tree-to-edges ι α) (α-to-edges ι α)]
  [(α-tree-to-edges ι (par α-tree_0 α-tree_1)) (appendT (α-tree-to-edges ι α-tree_0)
                                       (α-tree-to-edges ι α-tree_1))])

(define-metafunction coreLang
  writesMOedges : ι α-tree observedWrites -> ((vName vName) ...)
  [(writesMOedges ι α-tree observedWrites)
   (appendT (α-tree-to-edges ι α-tree)
            (observedWrites-to-edges ι observedWrites))])

(define (hasLoop edges)
  (ormap (λ (x) (> (length x) 1))
         (scc (unweighted-graph/directed edges))))

(define-metafunction coreLang
  removeγRestrictionsByVName : vName γ -> γ
  [(removeγRestrictionsByVName vName γ)
   ,(filter (λ (x) (match x [(list loc t name)
                             (not (equal? name (term vName)))]))
            (term γ))])

(define-metafunction coreLang
  updateByFrontMod : RM path ι τ σ σ-tree -> σ-tree
  [(updateByFrontMod acq path ι τ σ σ-tree) (updateByFront path σ σ-tree)]
  [(updateByFrontMod RM  path ι τ σ σ-tree) (updateByFront path ((ι τ)) σ-tree)])

(define-metafunction coreLang
  getDataDependenciesMod : RM ι σ η -> σ-dd
  [(getDataDependenciesMod con ι σ η) (getDataDependencies ι σ η)]
  [(getDataDependenciesMod RM  ι σ η) ()])

(define-metafunction coreLang
  resolveObservedWrite_lbl : path (vName ι) (vName ι τ) auxξ -> auxξ
  [(resolveObservedWrite_lbl path (vName ι) (vName ι τ) auxξ) auxξ_upd_readσ-tree
   (where σ-tree_old (getReadσ-tree auxξ))
   (where σ-tree_new (updateByFront path ((ι τ)) σ-tree_old))
   (where auxξ_upd_readσ-tree (updateState (Read σ-tree_old) (Read σ-tree_new) auxξ))]

  [(resolveObservedWrite_lbl path (vName_0 ι_0) (vName ι τ) auxξ) auxξ])

(define-metafunction coreLang
  deleteFromObservedWrites : vName observedWrites -> observedWrites
  [(deleteFromObservedWrites vName observedWriteList)
   (deleteFromObservedWriteList vName observedWriteList)]

  [(deleteFromObservedWrites vName (par observedWrites_0 observedWrites_1))
   (par (deleteFromObservedWrites vName observedWrites_0)
        (deleteFromObservedWrites vName observedWrites_1))])

(define-metafunction coreLang
  deleteFromObservedWriteLbl : vName  observedWriteLbl -> (observedWriteLbl ...)
  [(deleteFromObservedWriteLbl vName (vName ι)) ()]
  [(deleteFromObservedWriteLbl vName (par observedWrites_0 observedWrites_1))
   ((par (deleteFromObservedWrites vName observedWrites_0)
         (deleteFromObservedWrites vName observedWrites_1)))]
  [(deleteFromObservedWriteLbl vName observedWriteLbl) (observedWriteLbl)])

(define-metafunction coreLang
  deleteFromObservedWriteList : vName observedWriteList -> observedWriteList
  [(deleteFromObservedWriteList vName observedWriteList)
   ,(apply append (map (λ (x) (term (deleteFromObservedWriteLbl vName ,x)))
                       (term observedWriteList)))])

(define-metafunction coreLang
  resolveObservedWrite_path : path observedWrites (vName ι τ) auxξ -> auxξ
  [(resolveObservedWrite_path path (par observedWrites_0 observedWrites_1) (vName ι τ) auxξ)
   auxξ_1
   (where auxξ_0 (resolveObservedWrite_path (updatePath L path) observedWrites_0 (vName ι τ) auxξ))
   (where auxξ_1 (resolveObservedWrite_path (updatePath R path) observedWrites_1 (vName ι τ) auxξ_0))]

  [(resolveObservedWrite_path path observedWriteList (vName ι τ) auxξ)
   auxξ_new
   (where auxξ_upd_readσ-tree
          ,(foldl (λ (elem r) (term (resolveObservedWrite_lbl path ,elem (vName ι τ) ,r)))
                  (term auxξ)
                  (term (flat-ObservedWriteList observedWriteList))))

   (where observedWrites_old (getObservedWrites auxξ))
   (where observedWrites_new (updateOnPath
                              path
                              (deleteFromObservedWriteList vName observedWriteList)
                              observedWrites_old))

   (where auxξ_new (updateState (RW observedWrites_old)
                                (RW observedWrites_new)
                                auxξ_upd_readσ-tree))]

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

(define-syntax-rule (define-postRules lang defaultState)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (in-hole Eif (read RM ι-var σ-dd))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret  a            ))) auxξ_new))
        "read-postponed"
        (fresh a)
        (where path     (pathE E))
        (where α-tree        (getα-tree auxξ))
        (where α        (getByPath path α-tree))

        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (read a ι-var RM σ-dd) α))
        (where α-tree_new    (updateOnPath path α_new α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM)))))
   
   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-resolve"
        (where α-tree      (getα-tree auxξ))
        (where η      (getη auxξ))
        (where σ-tree_read (getReadσ-tree auxξ))
        
        (where (in-hole Ep α_thread) (getα-tree auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (where (in-hole El_0 (read vName ι RM σ-dd)) α)
        (where (in-hole El_1 (τ μ-value σ)) (getCellHistory ι η))
        (where path (pathEp Ep))

        (where σ-tree_read_new (updateByFrontMod RM path ι τ σ σ-tree_read))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree_read) (Read σ-tree_read_new) auxξ))

        (where σ-dd_new   (frontMerge σ-dd (getDataDependenciesMod RM ι σ η)))

        (where α_new      (substμα vName μ-value σ-dd_new (elToList El_0)))
        (where α-tree_new      (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_upd_α-tree (updateState (P α-tree) (P α-tree_new) auxξ_upd_σ-tree))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_new   (updateState (R γ) (R γ_new) auxξ_upd_α-tree))

        (where σ_read     (getByPath path σ-tree_read))
        (where σ_to-check (frontMerge σ_read σ-dd))
        (where τ_read-min (fromMaybe 0 (lookup ι σ_to-check)))
        
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        
        (where ifContext (getIfContext Eifα))
        (side-condition (term
                         (canPostponedReadBePerformed (vName ι RM σ-dd) σ_read α_thread ifContext γ τ))))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-resolve-speculative"
        (where α-tree      (getα-tree auxξ))
        
        (where (in-hole Ep α_thread) α-tree)
        (where (in-hole Eifα α) α_thread)
        (where (in-hole El_reader (read vName ι rlx σ-dd)) α)
        
        (where (in-hole Ep_writer α_write) α-tree)
        (where (in-hole El_writer (write vName_1 ι rlx μ-value)) α_write)
        ;; (side-condition (term (canPostponedWriteBePerformed (vName_1 ι) α_write)))

        (where path (pathEp Ep))
        (where path_writer (pathEp Ep_writer))
        (side-condition (not (equal? (term path) (term path_writer))))

        (side-condition (not (term (existSyncActions (elFirstPart El_reader)))))
        (side-condition (not (term (existSyncActions (elFirstPart El_writer)))))

        (where ifContext (getIfContext Eifα))
        (side-condition (term (canPostponedReadBePerformedWOτ (vName ι rlx σ-dd) α_thread ifContext)))

        (where σ-dd_new  σ-dd) 
        (where α_new      (substμα vName μ-value σ-dd_new
                                   (elToList El_reader)))
        (where α-tree_new      (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_upd_α-tree (updateState (P α-tree) (P α-tree_new) auxξ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_upd_γ (updateState (R γ) (R γ_new) auxξ_upd_α-tree))

        (where observedWrites       (getObservedWrites auxξ))
        (where observedWrites_check (snocOnPath path (vName_1 ι) observedWrites))

        (side-condition (not (hasLoop (term (writesMOedges ι α-tree observedWrites_check)))))

        (where observedWrites_new (snocOnPathIfNew path (vName_1 ι) observedWrites))
        (where auxξ_new           (updateState (RW observedWrites)
                                               (RW observedWrites_new)
                                               auxξ_upd_γ)))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value
                 (propagateDD_vName vName path σ-dd_new AST)) auxξ_new))
        "read-propagate"
        (where α-tree      (getα-tree auxξ))
        
        (where (in-hole Ep α_thread) α-tree)
        (where (in-hole Eifα α) α_thread)
        (where (in-hole El_reader (read vName ι rlx σ-dd)) α)
       
        (where Maybe (getWriteToPropagate_α ι ,(reverse (term (elFirstPart El_reader)))))
        (where (Just (write vName_1 ι WM μ-value))
               ,(if (equal? (term Maybe) 'None)
                    (term (getWriteToPropagate ι Eifα))
                    (term Maybe)))

        (where path (pathEp Ep))

        ;; (where ifContext (getIfContext Eifα))
        ;; (side-condition (term (canPostponedReadBePerformedWOτ (vName ι rlx σ-dd) α_thread ifContext)))

        (where σ-dd_new  σ-dd) 
        (where α_new      (substμα vName μ-value σ-dd_new
                                   (elToList El_reader)))
        (where α-tree_new      (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_upd_α-tree (updateState (P α-tree) (P α-tree_new) auxξ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_upd_γ (updateState (R γ) (R γ_new) auxξ_upd_α-tree))
        (where auxξ_new   auxξ_upd_γ)

        ;; (where observedWrites       (getObservedWrites auxξ))
        ;; (where observedWrites_check (snocOnPath path (vName_1 ι) observedWrites))

        ;; (side-condition (not (hasLoop (term (writesMOedges ι α-tree observedWrites_check)))))

        ;; (where observedWrites_new (snocOnPathIfNew path (vName_1 ι) observedWrites))
        ;; (where auxξ_new           (updateState (RW observedWrites)
                                               ;; (RW observedWrites_new)
                                               ;; auxξ_upd_γ))
        )

   ;; TODO: update the rule to the speculative reads
   (--> (AST auxξ)
        (stuck defaultState)
        "read-resolve-stuck"
        (where α-tree      (getα-tree auxξ))
        (where η      (getη auxξ))
        (where σ-tree_read (getReadσ-tree auxξ))
        (where (in-hole Ep α) (getα-tree auxξ))
        (where (in-hole El (read vName ι RM σ-dd)) α)
        (side-condition (not (term (isPEntryInConflictWithα (read vName ι) (elFirstPart El)))))
        
        (side-condition (term (isLocationUninitialized ι σ-dd (pathEp Ep) auxξ))))

   (-->  ((in-hole E (in-hole Eif ((ret μ) >>= (λ vName AST)))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (subst vName a AST)))         auxξ_new))
        ;; The substitution is needed to avoid collapse with previous
        ;; postponed operations.
        ">>=-subst-postpone"
        (where μ_simplified (calcμ μ))

        ;; μ can't be substituted immediately
        (side-condition (not (redex-match coreLang μ-subst (term μ_simplified))))

        ;; μ doesnt contain `choice` operator --- they should be resolved before
        ;; postponing.
        (side-condition (doesntContainChoice (term μ_simplified)))

        (fresh a)
        (where path     (pathE E))
        (where α-tree        (getα-tree auxξ))
        (where α        (getByPath path α-tree))

        (side-condition (term (isCorrectEif Eif α)))

        (where α_new    (appendToα Eif (let-in a μ_simplified) α))
        (where α-tree_new    (updateOnPath path α_new α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ)))

   (-->  (AST  auxξ)
        (normalize        
         ((subst vName μ-value AST) auxξ_new))
        ">>=-subst-resolve"

        (where (in-hole Ep α_thread) (getα-tree auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (where (in-hole El (let-in vName μ-value)) α)
        (where path (pathEp Ep))

        (where α_new    (substμα vName μ-value () (elToList El)))
        (where α-tree        (getα-tree auxξ))
        (where α-tree_new    (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ)))

   (-->  ((in-hole E (in-hole Eif (write WM ι-var μ))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret a            ))) auxξ_new))
        "write-postpone"
        (where μ_simplified (calcμ μ))

        ;; μ doesnt contain `choice` operator --- they should be resolved before
        ;; postponing.
        (side-condition (doesntContainChoice (term μ_simplified)))

        (fresh a)
        (where path     (pathE E))
        (where α-tree        (getα-tree auxξ))
        (where α        (getByPath path α-tree))

        (side-condition (term (isCorrectEif Eif α)))
        (side-condition (or (equal? (term WM) 'rlx)
                            (equal? (term WM) 'rel)))

        (where α_new    (appendToα Eif (write a ι-var WM μ_simplified) α))
        (where α-tree_new    (updateOnPath path α_new α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ)))

   (-->  (AST  auxξ)
        (normalize 
         ((subst vName μ-value AST) auxξ_new))
        "write-resolve"

        (where (in-hole Ep α_thread) (getα-tree auxξ))
        (where (in-hole Eifα α) α_thread)
        (side-condition (not (empty? (term α))))

        (side-condition (equal? (term Eifα) (term hole)))

        (where (in-hole El (write vName ι WM μ-value)) α)
        (side-condition (term
                         (canPostponedWriteBePerformed (vName ι) α)))
        (side-condition (term (isWriteTheOldest vName ι auxξ)))

        (where path (pathEp Ep))

        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        
        (where α_new      (substμα vName μ-value () (elToList El)))
        (where α-tree          (getα-tree auxξ))
        (where α-tree_new      (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_upd_α-tree (updateState (P α-tree) (P α-tree_new) auxξ))

        (where η       (getη auxξ))
        (where σ-tree_read  (getReadσ-tree auxξ))

        (where τ               (getNextTimestamp ι η))
        (where σ-tree_read_new      (updateByFront path ((ι τ)) σ-tree_read))
        (where auxξ_read_front (updateState (Read σ-tree_read) (Read σ-tree_read_new) auxξ_upd_α-tree))
        (where auxξ_upd_front  ,(if (equal? (term WM) 'rel)
                                    (term (synchronizeWriteFront path auxξ_read_front))
                                    (term auxξ_read_front)))

        (where σ_write    (getWriteσ path auxξ_upd_front))
        (where σ_ToWrite  ,(if (equal? (term WM) 'rel)
                               (term (getReadσ path auxξ_upd_front))
                               (term (updateFront ι τ (getσToWrite σ_write ι η)))))
        (where η_new      (updateCell  ι μ-value σ_ToWrite η))
        (where auxξ_upd_η (updateState η η_new auxξ_upd_front))
        
        (where auxξ_part1_γ (resolveWriteγ path vName ((ι τ)) auxξ_upd_η))
        (where γ_part1      (getγ auxξ_part1_γ))
        (where γ_part2      (removeγRestrictionsByVName vName γ_part1))
        (where auxξ_part2_γ (updateState (R γ_part1) (R γ_part2) auxξ_part1_γ))
        
        (where auxξ_upd_γ   (dupRelWriteRestrictions ι τ σ_write auxξ_part2_γ))

        (where auxξ_upd_γ_2 (add-γ-entries_α (elFirstPart El) ι τ auxξ_upd_γ))
        (where auxξ_upd_γ_3 (addObservedWritesToγ path ι τ WM auxξ_upd_γ_2))
        
        (where auxξ_upd_observedWrites (resolveObservedWrite (vName ι τ) auxξ_upd_γ_3))
        (where auxξ_new   auxξ_upd_observedWrites))

   (-->  ((in-hole E (in-hole Eif (if vName AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (chooseBranch number AST_0 AST_1))) auxξ_new))
        "if-speculation-branch-choice"
        (where α-tree (getα-tree auxξ))
        (where (in-hole Ep α_thread) α-tree)
        (where (in-hole Eifα (in-hole El (if vName number α_0 α_1))) α_thread)

        (where α_new (insertListInEl El (chooseBranch number α_0 α_1)))
        (where path (pathE E))
        (where α-tree_new (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ)))
  
   (-->  ((in-hole E (in-hole Eif (if Expr AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (if a    AST_0 AST_1))) auxξ_new))
        "if-speculation-init"
        
        (where Expr_simplified (calc Expr))
        (side-condition (not (redex-match coreLang number (term Expr_simplified))))

        (where path     (pathE E))
        (where α-tree        (getα-tree auxξ))
        (where α        (getByPath path α-tree))
        (side-condition (not (term (is-if-in-α Expr_simplified α))))

        (fresh a)
        (where α_new    (appendToα Eif (if a Expr_simplified () ()) α))
        (where α-tree_new    (updateOnPath path α_new α-tree))
        (where auxξ_new (updateState (P α-tree) (P α-tree_new) auxξ)))
   
   (-->  (AST auxξ)
        (normalize
         ((subst vName_2 a (subst vName_1 a AST)) auxξ_new))
        "if-speculation-write-promoting"

        (where (in-hole Ep α_thread) (getα-tree auxξ))
        (where (in-hole Eifα α) α_thread)
        
        (where (in-hole El_0 (if vName_0 Expr α_1 α_2)) α)
        (where (in-hole El_1 (write vName_1 ι WM μ-value)) α_1)
        (where (in-hole El_2 (write vName_2 ι WM μ-value)) α_2)

        (side-condition (term
                         (canPostponedWriteBePerformed (vName_1 ι) α_1)))
        (side-condition (term
                         (canPostponedWriteBePerformed (vName_2 ι) α_2)))


        (fresh a)
        (where α_1_new (substμα vName_1 a () (elToList El_1)))
        (where α_2_new (substμα vName_2 a () (elToList El_2)))

        (where α_new (insertListInEl El_0
                      ((write a ι WM μ-value)
                       (if vName_0 Expr α_1_new α_2_new))))

        (where path     (pathEp Ep))
        (where α-tree          (getα-tree auxξ))
        (where α-tree_new      (updateOnPath path (in-hole Eifα α_new) α-tree))
        (where auxξ_new   (updateState (P α-tree) (P α-tree_new) auxξ)))

   ;; Leads to very poor performance, but solves an issue with tests from etaPsi2SCpostLangTests.rkt
   ;; (-->  ((in-hole E (par (ret μ_0) (ret μ_1)))              auxξ)
   ;;      (normalize 
   ;;       ((in-hole E (ret (    μ_0       μ_1))) (joinST path auxξ_new)))
   ;;      "join-postponed-operations-interleaving"
   ;;      (where path (pathE E))

   ;;      (where α-tree             (getα-tree auxξ))
   ;;      (where (par α_0 α_1) (getByPath path α-tree))
   ;;      (where (in-hole El α_interleaved) ,(interleavings (term α_0) (term α_1)))
   ;;      (where α-tree_new         (updateOnPath path α_interleaved α-tree))
   ;;      (where auxξ_upd_α-tree    (updateState (P α-tree) (P α-tree_new) auxξ))
        
   ;;      (where observedWrites (getObservedWrites auxξ))
   ;;      (where (par observedWrites_0 observedWrites_1) (getByPath path observedWrites_old))
   ;;      (where observedWrites_new (updateOnPath path ((par observedWrites_0 observedWrites_1))
   ;;                                              observedWrites_old))

   ;;      (where auxξ_new (updateState (RW observedWrites)
   ;;                                   (RW observedWrites_new)
   ;;                                   auxξ_upd_α-tree)))
)))
