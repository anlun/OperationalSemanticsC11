#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-postponedReadRules) 

(define-metafunction coreLang
  removeγRestrictionsByVName : vName γ -> γ
  [(removeγRestrictionsByVName vName γ)
   ,(filter (λ (x) (match x [(list loc t name)
                             (not (equal? name (term vName)))]))
            (term γ))])

(define-metafunction coreLang
  updateByFrontMod : RM path σ ψ -> ψ
  [(updateByFrontMod acq path σ ψ) (updateByFront path σ ψ)]
  [(updateByFrontMod RM  path σ ψ) ψ])

(define-metafunction coreLang
  getDataDependenciesMod : RM ι σ η -> σ-dd
  [(getDataDependenciesMod con ι σ η) (getDataDependencies ι σ η)]
  [(getDataDependenciesMod RM  ι σ η) ()])

;; TODO: Rewrite to tree traversal.
;; The current implementation doesn't work correctly
;; if a program contains a variable with name `choice`. 
(define (doesntContainChoice mu) ;; μ -> boolean
  (not (memv 'choice (flatten mu))))

(define-metafunction coreLang
  appendToα : Eif postponedEntry α -> α
  [(appendToα Eif1 postponedEntry α) (appendT α (postponedEntry))]

  [(appendToα (if vName Eif AST) postponedEntry (any_0 ... (if vName Expr α_0 α_1) any_1 ...))
   (any_0 ... (if vName Expr (appendToα Eif postponedEntry α_0) α_1) any_1 ...)]

  [(appendToα (if vName AST Eif) postponedEntry (any_0 ... (if vName Expr α_0 α_1) any_1 ...))
   (any_0 ... (if vName Expr α_0 (appendToα Eif postponedEntry α_1)) any_1 ...)])

(define-metafunction coreLang
  branchChoose : number any any -> any
  [(branchChoose 0      any_0 any_1) any_1]
  [(branchChoose number any_0 any_1) any_0])

(define-metafunction coreLang
  insertListInEl : El (any ...) -> (any ...)
  [(insertListInEl (any_0 ... hole any_1 ...) any) (appendT (any_0 ...) (appendT any (any_1 ...)))])

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
        (side-condition (term (isPossibleE E auxξ))))

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
        (side-condition (term (isPossibleE E auxξ))))

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

        (where ψ_read_new (updateByFrontMod RM path σ ψ_read))
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
        
        (side-condition (term
                         (canPostponedReadBePerformed (vName ι RM σ-dd) σ_read α γ τ)))
      
        (where ifContext (getIfContext Eifα))
        (side-condition (term (isPossibleRead path vName ι τ_read-min τ ifContext auxξ))))

   ;; TODO: update the rule to the speculative reads
   (--> (AST auxξ)
        (stuck defaultState)
        "read-resolve-stuck"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El_0 (read vName ι RM σ-dd)) α)
        (side-condition (not (empty? (term α))))        
        (side-condition (term (isFirstRecord vName ι α)))
        
        (where path (pathEp Ep))
        (side-condition (term (isLocationUninitialized ι σ-dd path auxξ))))

   (-->  ((in-hole E (in-hole Eif ((ret μ) >>= (λ vName AST)))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (subst vName a AST)))         auxξ_new))
        ;; The substitution is needed to avoid collapse with previous
        ;; postponed operations.
        ">>=-subst-postpone"
        (side-condition (term (isPossibleE E auxξ)))
        
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
        (side-condition (term (isPossiblePath path auxξ))))

   (-->  ((in-hole E (in-hole Eif (write rlx ι-var μ))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (ret a            ))) auxξ_new))
        "write-rlx-postpone"
        (side-condition (term (isPossibleE E auxξ)))
        
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

        (where path (pathEp Ep))
        (side-condition (term (isPossiblePath path auxξ)))

        (where (in-hole El (write vName ι WM μ-value)) α)
        (side-condition (term
                         (canPostponedWriteBePerformed (vName ι) α)))

        (where α_new      (substμα vName μ-value () (elToList El)))
        (where φ          (getφ auxξ))
        (where φ_new      (updateOnPath path (in-hole Eifα α_new) φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ))

        (where η       (getη auxξ))
        (where ψ_read  (getReadψ auxξ))

        (where τ              (getNextTimestamp ι η))
        (where ψ_read_new     (updateByFront path ((ι τ)) ψ_read))
        (where auxξ_upd_front (updateState (Read ψ_read) (Read ψ_read_new) auxξ_upd_φ))

        (where σ_write    (getWriteσ path auxξ))
        (where σ_ToWrite  (updateFront ι τ (getσToWrite σ_write ι η)))
        (where η_new      (updateCell  ι μ-value σ_ToWrite η))
        (where auxξ_upd_η (updateState η η_new auxξ_upd_front))
        (where auxξ_upd_γ (dupRelWriteRestrictions ι τ σ_write auxξ_upd_η))
        (where auxξ_new   auxξ_upd_γ))

   (-->  ((in-hole E (in-hole Eif (if vName AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (branchChoose number AST_0 AST_1))) auxξ_new))
        "if-speculation-branch-choice"

        (where path (pathE E))
        (side-condition (term (isPossiblePath path auxξ)))

        (where φ (getφ auxξ))
        (where (in-hole Ep α_thread) φ)
        (where (in-hole Eifα (in-hole El (if vName number α_0 α_1))) α_thread)

        (where α_new (insertListInEl El (branchChoose number α_0 α_1)))
        (where φ_new (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ)))
  
   (-->  ((in-hole E (in-hole Eif (if Expr AST_0 AST_1))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (if a    AST_0 AST_1))) auxξ_new))
        "if-speculation-init"
        
        (side-condition (term (isPossiblePath (pathE E) auxξ)))
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
                         (canPostponedWriteBePerformed (vName_1 ι) α_1)))
        (side-condition (term
                         (canPostponedWriteBePerformed (vName_2 ι) α_2)))

        (where path (pathEp Ep))
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

;; TODO
;; 1) Add buffer-propagation rule.

)))
