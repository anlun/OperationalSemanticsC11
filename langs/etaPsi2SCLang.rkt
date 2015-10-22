#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")

(define-extended-language etaPsi2SCLang coreLang
  ; State:
  ; AST       -- current state of program tree;
  ; η         -- current heap history;
  ; (Read  ψ) -- current threads read  fronts;
  ; (Write ψ) -- current threads write fronts;
  ; (SC σ)    -- front after last SC operation;
  ; θ         -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (Write ψ) θ ... (SC σ) θ ...)])

(define-term defaultState (() (Read ()) (Write ()) (SC ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_2ψ joinST_2ψ isReadQueueEqualTo_t)
   etaPsi2SCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define rlxReadRules  (define-rlxReadRules  etaPsi2SCLang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2SCLang
                        getWriteσ_2ψ isReadQueueEqualTo_t ιNotInReadQueue_t))
(define relAcqRules   (define-relAcqRules   etaPsi2SCLang
                        addReadNode_t
                        synchronizeWriteFront isReadQueueEqualTo_t addWriteNode_t))
(define naRules       (define-naRules       etaPsi2SCLang
                       addReadNode_t
                       defaultState getWriteσ_2ψ ιNotInReadQueue
                       addWriteNode_t))
(define scRules       (define-scRules     etaPsi2SCLang
                       getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo_t))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules scRules))
