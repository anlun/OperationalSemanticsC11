#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
;(require "rlxRules.rkt")
(provide etaPsi2Lang coreStep defaultState)

(define-extended-language etaPsi2Lang coreLang
  ; State:
  ; AST       -- current state of program tree;
  ; η         -- current heap history;
  ; (Read  ψ) -- current threads read  fronts;
  ; (Write ψ) -- current threads write fronts;
  ; θ         -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (Write ψ) θ ...)])

(define-term defaultState (() (Read ()) (Write ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_2ψ joinST_2ψ isReadQueueEqualTo_t)
   etaPsi2Lang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

#|
(define rlxRules (define-rlxRules etaPsi2Lang getWriteσ_2ψ))
(define step (union-reduction-relations coreStep rlxRules))
|#
