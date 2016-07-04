#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/postReadRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")
(require "../core/langs.rkt")
(provide defaultState step randomStep)

(define-term defaultState (() (Read ()) (NA ()) (Write ()) (SC ()) (P ()) (R ()) (RW ()) (RWD ()) (RWS ()) (Deallocated ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST-2ψ-φ joinST-2ψ-φ isReadQueueEqualTo)
   etaPsi2SCpostLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define postponedReadRules (define-postponedReadRules etaPsi2SCpostLang
                             defaultState getWriteσ_2ψ))
(define rlxWriteRules      (define-rlxWriteRules      etaPsi2SCpostLang
                             getWriteσ_2ψ isReadQueueEqualTo ιNotInReadQueue))
(define relAcqWriteRules   (define-relAcqWriteRules   etaPsi2SCpostLang
                             addReadNode_t
                             synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue 
                             addWriteNode_t))
(define naRules            (define-naWriteStuckRules  etaPsi2SCpostLang
                             defaultState getWriteσ_2ψ ιNotInReadQueue addWriteNode_t))
(define scRules            (define-scRules            etaPsi2SCpostLang
                             getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue))
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
