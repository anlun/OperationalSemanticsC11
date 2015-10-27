#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide postReadLang postponedReadCoreStep postponedReadDefaultState)

(define-extended-language postReadLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; φ        -- component for postponed reads;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (P φ) θ ...)])

(define-term postponedReadDefaultState (() (Read ()) (P ())))
(define postponedReadCoreStep
  (extend-reduction-relation
   (define-coreStep postponedReadDefaultState spwST_readψ_φ joinST_readψ_φ isReadQueueEqualTo)
   postReadLang #:domain ξ))
(define postponedReadCoreTest (define-coreTest postponedReadCoreStep postponedReadDefaultState))
