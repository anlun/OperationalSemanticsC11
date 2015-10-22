#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/pp.rkt")
(require "../tests/testTerms.rkt")

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-term initialGraph  (Graph  (((0 skip)) ())))
(define-term initialGFront (GFront 0))

(define-term defaultState (() initialGraph initialGFront))

(define coreStep (define-coreStep defaultState spwST_gr joinST_gr isReadQueueEqualTo_t))
(define coreTest (define-coreTest coreStep defaultState))

;(traces coreStep (term (,testTerm-1 defaultState)) #:pp pretty-printer)
