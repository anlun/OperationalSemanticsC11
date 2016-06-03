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

(define-syntax-rule (define-postponedReadRules lang defaultState)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (read RM ι-var)) auxξ)
        (normalize
         ((in-hole E (ret  a       )) auxξ_new))
        "read-postponed"
        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))
        (where α_new    ,(append (term α) (term ((a ι-var RM ())))))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM))))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (readCon RM ι-var σ-dd)) auxξ)
        (normalize
         ((in-hole E (ret          a       )) auxξ_new))
        "readCon-postponed"
        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))
        (where α_new    ,(append (term α) (term ((a ι-var RM σ-dd)))))
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
        
        (where (in-hole Ep α) (getφ auxξ))
        (side-condition (not (empty? (term α))))

        (where (in-hole El_0 (vName ι RM σ-dd)) α)
        (where (in-hole El_1 (τ μ-value σ)) (getCellHistory ι η))
        (where path (pathEp Ep))

        (where ψ_read_new (updateByFrontMod RM path σ ψ_read))
        (where auxξ_upd_ψ (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ-dd_new   (frontMerge σ-dd (getDataDependenciesMod RM ι σ η)))

        (where α_new      (substμα vName μ-value σ-dd_new (elToList El_0)))
        (where φ_new      (updateOnPath path α_new φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ_upd_ψ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_new   (updateState (R γ) (R γ_new) auxξ_upd_φ))

        (where σ_read     (getByPath path ψ_read))
        (where σ_to-check (frontMerge σ_read σ-dd))
        (where τ_read-min (fromMaybe 0 (lookup ι σ_to-check)))
        
        (side-condition (term
                         (canPostponedReadBePerformed (vName ι RM σ-dd) σ_read α γ τ)))
       
        (side-condition (term (isPossibleRead path vName ι τ_read-min τ auxξ))))

   (--> (AST auxξ)
        (stuck defaultState)
        "read-resolve-stuck"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El_0 (vName ι RM σ-dd)) α)
        (side-condition (not (empty? (term α))))        
        (side-condition (term (isFirstRecord vName ι α)))
        
        (where path (pathEp Ep))
        (side-condition (term (isLocationUninitialized ι σ-dd path auxξ))))

   ;; (-->  ((in-hole E ((ret μ) >>= (λ vName AST))) auxξ)
   ;;       ((in-hole E AST)         auxξ)
   ;;      ">>=-subst-postpone"
   ;;      (side-condition (term (isPossibleE E auxξ)))
   ;;      (sude-condition (not (redex-match coreLang μ (term μ))))
   ;;      ) 
)))
