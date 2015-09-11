#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/rlxRules.rkt")
(require "../tests/testTerms.rkt")
(require "../core/pp.rkt")
(provide define-postponedReadRules)

(define-extended-language postReadLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; φ        -- component for postponed reads;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (P φ) θ ...)])

(define-term defaultState (() (Read ()) (P ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_readψ_φ joinST_readψ_φ isReadQueueEqualTo)
   postReadLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define-syntax-rule (define-postponedReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (--> ((in-hole E (read RM ι-var)) auxξ)
        ((in-hole E (ret  a       )) auxξ_new)
        "read-postponed"
        (fresh a)
        (where path     (pathE E))
        (where φ        (getφ auxξ))
        (where α        (getByPath path φ))
        (where α_new    ,(append (term α) (term ((a ι-var RM)))))
        (where φ_new    (updateOnPath path α_new φ))
        (where auxξ_new (updateState (P φ) (P φ_new) auxξ))

        (side-condition (not (equal? (term sc) (term RM)))))

   (--> (                     AST  auxξ)
        ((subst vName μ-value AST) auxξ_new)
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
        
        (side-condition (term (isLocationUninitialized ι auxξ))))

)))

(define postponedReadRules (define-postponedReadRules postReadLang))
(define rlxWriteRules      (define-rlxWriteRules      postReadLang
                             getWriteσ_nil isReadQueueEqualTo ιNotInReadQueue))
(define step               (union-reduction-relations coreStep rlxWriteRules postponedReadRules))

(test-->>∃ step
          (term (,testTerm0  defaultState))
          (term ((ret (0 0)) defaultState)))

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#

(traces step (term (,testTerm0 defaultState)) #:pp pretty-printer)

(test-->>∃ step
          (term (,testTerm01 defaultState))
          (term ((ret (1 1)) defaultState)))