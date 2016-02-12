#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-postponedReadRules) 

(define-metafunction coreLang
  isRestrictedByγ : ι τ RM γ -> boolean
  [(isRestrictedByγ ι τ RM (any_0 ... (ι τ vName) any_1 ...)) #t
   (side-condition (mo<=? (term acq) (term RM)))]
  [(isRestrictedByγ ι τ RM γ) #f])

(define-metafunction coreLang
  removeγRestrictionsByVName : vName γ -> γ
  [(removeγRestrictionsByVName vName γ)
   ,(filter (λ (x) (match x [(list loc t name)
                             (not (equal? name (term vName)))]))
            (term γ))])

(define-syntax-rule (define-postponedReadRules lang)
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

        (side-condition (not (equal? (term sc) (term RM)))))

   ; TODO: propagate information at the moment of resolving consume read.
   (-->  (                     AST  auxξ)
        (normalize        
         ((subst vName μ-value AST) auxξ_new))
        "read-resolve"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El_0 (vName ι RM σ-dd)) α)
        (where (in-hole El_1 (τ μ-value σ)) (getCellHistory ι η))
        (where path (pathEp Ep))

        (where ψ_read_new (updateByFront path σ ψ_read))
        (where auxξ_upd_ψ (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where α_new      (substμα vName μ-value (elToList El_0)))
        (where φ_new      (updateOnPath path α_new φ))
        (where auxξ_upd_φ (updateState (P φ) (P φ_new) auxξ_upd_ψ))

        (where γ          (getγ auxξ))
        (where γ_new      (removeγRestrictionsByVName vName γ))
        (where auxξ_new   (updateState (R γ) (R γ_new) auxξ_upd_φ))

        (where σ_read   (getByPath path ψ_read))
        (side-condition (not (empty? (term α))))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ-dd))))
        (side-condition (term (isFirstRecord vName ι α)))

        (side-condition (not (term (isRestrictedByγ ι τ RM γ)))))

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
        
        (side-condition (term (isLocationUninitialized ι auxξ)))))))
