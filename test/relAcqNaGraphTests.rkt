#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")
(require "../core/pp.rkt")
(require "../core/graphUtils.rkt")
(require "../core/langs.rkt")

(define-term initialGraph  (Graph  (((0 skip)) ())))
(define-term initialGFront (GFront 0))

(define-term defaultState (() (Read ()) initialGraph initialGFront))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_readψ_gr joinST_readψ_gr isReadQueueEqualTo_t)
   etaPsiGraphLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define relAcqRules (define-relAcqRules etaPsiGraphLang
                      addReadNode
                      synchronizeWriteFront_id isReadQueueEqualTo_t
                      addWriteNode))
(define naRules     (define-naRules     etaPsiGraphLang
                      addReadNode
                      defaultState getWriteσ_nil ιNotInReadQueue_t
                      addWriteNode))
(define step        (union-reduction-relations coreStep relAcqRules naRules))

#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rel = 0;
               y_rel = 0;
x_rel = 1;         || y_rel = 1;
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(test-->>∃ step
         (term (,testTerm4 defaultState))
         (term (stuck defaultState)))

;(traces step (term (,testTerm4 defaultState)) #:pp pretty-printer)
;(stepper step (term (,testTerm4 defaultState)) pretty-printer)
;(stepper step (term (,testTerm3-3 defaultState)) pretty-printer)