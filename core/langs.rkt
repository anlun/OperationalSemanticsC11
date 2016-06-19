#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide etaPsiLang etaPsiCoreStep etaPsiCoreStep etaPsiDefaultState 
         postReadLang postponedReadCoreStep postponedReadDefaultState

         etaPsi2Lang
         etaPsiSCLang etaPsi2SCLang etaPsi2SCpostLang
         graphLang etaPsiGraphLang

         schedulerLang
         schedulerCoreStep
         schedulerDefaultState
)

(define-extended-language etaPsiLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; (NA   σ) -- location -> last NA write on it;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (NA σ) θ ...)])

(define-term etaPsiDefaultState (() (Read ()) (NA ())))

(define etaPsiCoreStep
  (extend-reduction-relation
    (define-coreStep etaPsiDefaultState spwST-readψ joinST-readψ isReadQueueEqualTo_t)
   etaPsiLang #:domain ξ))
(define etaPsiCoreTest (define-coreTest etaPsiCoreStep etaPsiDefaultState))

(define-extended-language etaPsiSCLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;  
  ; (NA   σ) -- location -> last NA write on it;
  ; (SC σ)   -- front after last SC operation;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (NA σ) θ ... (SC σ) θ ...)])

(define-extended-language etaPsi2Lang coreLang
  ; State:
  ; AST       -- current state of program tree;
  ; η         -- current heap history;
  ; (Read  ψ) -- current threads read  fronts;
  ; (NA    σ) -- location -> last NA write on it;
  ; (Write ψ) -- current threads write fronts;
  ; θ         -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (NA σ) θ ... (Write ψ) θ ...)])

(define-extended-language etaPsi2SCLang coreLang
  ; State:
  ; AST       -- current state of program tree;
  ; η         -- current heap history;
  ; (Read  ψ) -- current threads read  fronts;
  ; (NA    σ) -- location -> last NA write on it;
  ; (Write ψ) -- current threads write fronts;
  ; (SC σ)    -- front after last SC operation;
  ; θ         -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (NA σ) θ ... (Write ψ) θ ... (SC σ) θ ...)])

(define-extended-language postReadLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; (NA   σ) -- location -> last NA write on it;
  ; (P    φ) -- component with thread-specific information about postponed reads;
  ; (R    γ) -- component with restiction on a resolve order for postponed reads;
  ; (RW   observedWrites) -- (path, ι) -> observed uncommitted to history writes.
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (NA σ) θ ... (P φ) θ ... (R γ) θ ... (RW observedWrites) θ ... (Deallocated listι) θ ...)])

(define-term postponedReadDefaultState (() (Read ()) (NA ()) (P ()) (R ()) (RW ()) (Deallocated ())))
(define postponedReadCoreStep
  (extend-reduction-relation
   (define-coreStep postponedReadDefaultState spwST-readψ-φ joinST-readψ-φ isReadQueueEqualTo)
   postReadLang #:domain ξ))
(define postponedReadCoreTest (define-coreTest postponedReadCoreStep postponedReadDefaultState))

(define-extended-language etaPsi2SCpostLang coreLang
  [auxξ (η (Read ψ) (NA σ) (Write ψ) (SC σ) (P φ) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language schedulerLang coreLang
  [auxξ (η (Read ψ) (NA σ) (Write ψ) (SC σ) (P φ) (R γ) (RW observedWrites) (Paths pathsτ) (Deallocated listι))])
(define-term schedulerDefaultState
  (() (Read ()) (NA ()) (Write ()) (SC ()) (P ()) (R ()) (RW ()) (Paths ()) (Deallocated ())))
(define schedulerCoreStep
  (extend-reduction-relation
   (define-coreStep schedulerDefaultState spwST-2ψ-φ joinST-2ψ-φ isReadQueueEqualTo)
   schedulerLang #:domain ξ))

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-extended-language etaPsiGraphLang coreLang
  ; State:
  ; AST         -- current state of program tree;
  ; η           -- current heap history;
  ; (Read ψ)    -- current threads read fronts;
  ; (NA   σ)    -- location -> last NA write on it;
  ; (Graph G)   -- current graph of memory actions;
  ; (GFront GF) -- thread positions in the graph;
  ; θ           -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) (NA σ) θ ... θ ... (Graph G) (GFront GF) θ ...)])
