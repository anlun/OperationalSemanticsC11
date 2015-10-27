#lang racket
(require redex/reduction-semantics)
(require "../core/coreUtils.rkt")
(require "../langs/etaPsiLang.rkt")
(require "../tests/testTerms.rkt")
(require "naRules.rkt")

(define naRules
  (define-naRules etaPsiLang addReadNode_t defaultState getWriteσ_nil ιNotInReadQueue_t addWriteNode_t))

(define naStep
  (union-reduction-relations coreStep naRules))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(test-->>∃ naStep
          (term (,testTerm2 defaultState))
          (term (stuck defaultState)))
