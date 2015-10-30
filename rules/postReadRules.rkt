#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-postponedReadRules) 

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
        (where α_new    ,(append (term α) (term ((a ι-var RM)))))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM)))))

   (-->  (                     AST  auxξ)
        (normalize        
         ((subst vName μ-value AST) auxξ_new))
        "read-resolve"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El_0 (vName ι RM)) α)
        (where (in-hole El_1 (τ μ-value σ)) (getCellHistory ι η))
        (where path (pathEp Ep))

        (where ψ_read_new (updateByFront path σ ψ_read))
        (where auxξ_upd_ψ (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where α_new      (substμα vName μ-value (elToList El_0)))
        (where φ_new      (updateOnPath path α_new φ))
        (where auxξ_new   (updateState (P φ) (P φ_new) auxξ_upd_ψ))

        (where σ_read   (getByPath path ψ_read))
        (side-condition (not (empty? (term α))))
        (side-condition (term (correctτ τ ι σ_read)))
        (side-condition (term (isFirstRecord vName ι α))))

   (--> (AST auxξ)
        (stuck defaultState)
        "read-resolve-stuck"
        (where φ      (getφ auxξ))
        (where η      (getη auxξ))
        (where ψ_read (getReadψ auxξ))
        (where (in-hole Ep α) (getφ auxξ))
        (where (in-hole El_0 (vName ι RM)) α)
        (side-condition (not (empty? (term α))))        
        (side-condition (term (isFirstRecord vName ι α)))
        
        (side-condition (term (isLocationUninitialized ι auxξ)))))))
