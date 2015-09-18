#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")

(define-extended-language graphLang coreLang
  [auxξ (θ ... η θ ... (Graph G) (GFront GF) θ ...)])

(define-term initialGraph  (Graph  ((0 skip) ())))
(define-term initialGFront (GFront 0))

(define-term defaultState (() initialGraph initial GFront))

(define step (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t))