#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide etaPsiGraphLang coreStep defaultState)

(define-extended-language etaPsiGraphLang coreLang
  ; State:
  ; AST         -- current state of program tree;
  ; η           -- current heap history;
  ; (Read ψ)    -- current threads read fronts;
  ; (Graph G)   -- current graph of memory actions;
  ; (GFront GF) -- thread positions in the graph;
  ; θ           -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (Graph G) (GFront GF) θ ...)])

(define-term initialGraph  (Graph  (((0 skip)) ())))
(define-term initialGFront (GFront 0))

(define-term defaultState (() (Read ()) initialGraph initialGFront))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_readψ_gr joinST_readψ_gr isReadQueueEqualTo_t)
   etaPsiGraphLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))
