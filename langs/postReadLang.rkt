#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide etaPsiLang etaPsiCoreStep etaPsiCoreStep etaPsiDefaultState 
         postReadLang postponedReadCoreStep postponedReadDefaultState
         
         etaPsi2SCLang
         etaPsi2SCpostLang graphLang
         etaPsiGraphLang)

(define-extended-language etaPsiLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ...)])

(define-term etaPsiDefaultState (() (Read ())))

(define etaPsiCoreStep
  (extend-reduction-relation
   (define-coreStep etaPsiDefaultState spwST_readψ joinST_readψ isReadQueueEqualTo_t)
   etaPsiLang #:domain ξ))
(define etaPsiCoreTest (define-coreTest etaPsiCoreStep etaPsiDefaultState))

(define-extended-language etaPsi2SCLang coreLang
  ; State:
  ; AST       -- current state of program tree;
  ; η         -- current heap history;
  ; (Read  ψ) -- current threads read  fronts;
  ; (Write ψ) -- current threads write fronts;
  ; (SC σ)    -- front after last SC operation;
  ; θ         -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (Write ψ) θ ... (SC σ) θ ...)])

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

(define-extended-language etaPsi2SCpostLang coreLang
  [auxξ (η (Read ψ) (Write ψ) (SC σ) (P φ))])

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-extended-language etaPsiGraphLang coreLang
  ; State:
  ; AST         -- current state of program tree;
  ; η           -- current heap history;
  ; (Read ψ)    -- current threads read fronts;
  ; (Graph G)   -- current graph of memory actions;
  ; (GFront GF) -- thread positions in the graph;
  ; θ           -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (Graph G) (GFront GF) θ ...)])
