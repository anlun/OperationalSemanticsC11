#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide etaPsiLang coreStep defaultState)

(define-extended-language etaPsiLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ...)])

(define-term defaultState (() (Read ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_readψ joinST_readψ isReadQueueEqualTo_t)
   etaPsiLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))
