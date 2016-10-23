#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/postRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")
(require "../core/langs.rkt")
(provide defaultState step randomStep)

(define-term defaultState (() (Read ()) (AcqFront ()) (RelFront ()) (NA ()) (Write ()) (SC ()) (P ()) (R ()) (RW ()) (Deallocated ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState)
   etaPsi2SCpostLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define postponedReadRules (define-postponedReadRules etaPsi2SCpostLang defaultState))
(define rlxWriteRules      (define-rlxWriteRules      etaPsi2SCpostLang))
(define relAcqWriteRules   (define-relAcqWriteRules   etaPsi2SCpostLang))
(define naRules            (define-naWriteStuckRules  etaPsi2SCpostLang defaultState))
(define scRules            (define-scRules            etaPsi2SCpostLang))
(define step (union-reduction-relations
              coreStep
              postponedReadRules
              rlxWriteRules
              relAcqWriteRules
              naRules
              scRules))

(define-syntax-rule (define-randomStep step)
  (begin
    (reduction-relation coreLang #:domain ξ
     (--> ξ ξ_new
          "random-step"
          (where listξ ,(filter (λ (x) (not (equal? 'stuck (car x))))
                                (apply-reduction-relation step (term ξ))))
          (side-condition (> (length (term listξ)) 0))
          (where ξ_new ,(select-random (term listξ))))

     (--> ξ (stuck defaultState)
          "random-step-stuck"
          (where (in-hole El (stuck auxξ)) ,(apply-reduction-relation step (term ξ))))
)))

(define randomStep (define-randomStep step))
