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
)

(define-extended-language etaPsiLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; (NA   σ) -- location -> last NA write on it.
  [auxξ (η (Read ψ) (NA σ))])

(define-term etaPsiDefaultState (() (Read ()) (NA ())))

(define etaPsiCoreStep
  (extend-reduction-relation
    (define-coreStep etaPsiDefaultState spwST-readψ joinST-readψ)
   etaPsiLang #:domain ξ))
(define etaPsiCoreTest (define-coreTest etaPsiCoreStep etaPsiDefaultState))

(define-extended-language etaPsiSCLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;  
  ; (NA   σ) -- location -> last NA write on it;
  ; (SC σ)   -- front after last SC operation.
  [auxξ (η (Read ψ) (NA σ) (SC σ))])

(define-extended-language etaPsi2Lang coreLang
  ; State:
  ; AST          -- current state of program tree;
  ; η            -- current heap history;
  ; (Read  ψ)         -- per-thread read    fronts;
  ; (AcqFront ψ)      -- per-thread acquire fronts;
  ; (RelFront χ-tree) -- per-thread release fronts;
  ; (NA    σ)    -- location -> last NA write on it;
  ; (Write ψ)    -- current threads write fronts.
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ))])

(define-extended-language etaPsi2SCLang coreLang
  ; State:
  ; AST               -- current state of program tree;
  ; η                 -- current heap history;
  ; (Read  ψ)         -- per-thread read    fronts;
  ; (AcqFront ψ)      -- per-thread acquire fronts;
  ; (RelFront χ-tree) -- per-thread release fronts;
  ; (NA    σ)         -- location -> last NA write on it;
  ; (Write ψ)         -- current threads write fronts;
  ; (SC σ)            -- front after last SC operation.
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ) (SC σ))])

(define-extended-language postReadLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;
  ; (NA   σ) -- location -> last NA write on it;
  ; (P    φ) -- component with thread-specific information about postponed reads;
  ; (R    γ) -- component with restiction on a resolve order for postponed reads;
  ; (RW   observedWrites) -- (path, ι) -> observed uncommitted to history writes.
  [auxξ (η (Read ψ) (NA σ) (P φ) (R γ) (RW observedWrites) (Deallocated listι))])

(define-term postponedReadDefaultState (() (Read ()) (NA ()) (P ()) (R ()) (RW ()) (Deallocated ())))
(define postponedReadCoreStep
  (extend-reduction-relation
   (define-coreStep postponedReadDefaultState spwST-readψ-φ joinST-readψ-φ)
   postReadLang #:domain ξ))
(define postponedReadCoreTest (define-coreTest postponedReadCoreStep postponedReadDefaultState))

(define-extended-language etaPsi2SCpostLang coreLang
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ) (SC σ) (P φ) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-extended-language etaPsiGraphLang coreLang
  ; State:
  ; AST         -- current state of program tree;
  ; η           -- current heap history;
  ; (Read ψ)    -- current threads read fronts;
  ; (NA   σ)    -- location -> last NA write on it;
  ; (Graph G)   -- current graph of memory actions;
  ; (GFront GF) -- thread positions in the graph.
  [auxξ (η (Read ψ) (NA σ) (Graph G) (GFront GF))])
