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

; State:
; AST                   -- current state of program tree;
; η                     -- current heap history;
; (Read  ψ)             -- per-thread read    fronts;
; (AcqFront ψ)          -- per-thread acquire fronts;
; (RelFront χ-tree)     -- per-thread release fronts;
; (NA    σ)             -- location -> last NA write on it;
; (Write ψ)             -- current threads write fronts;
; (SC σ)                -- front after last SC operation.
; (P    φ)              -- component with thread-specific information about postponed reads;
; (R    γ)              -- component with restiction on a resolve order for postponed reads;
; (RW   observedWrites) -- (path, ι) -> observed uncommitted to history writes.

; (Graph G)             -- current graph of memory actions;
; (GFront GF)           -- thread positions in the graph.

(define-extended-language etaPsiLang coreLang
  [auxξ (η (Read ψ) (NA σ))])

(define-extended-language etaPsiSCLang coreLang
  [auxξ (η (Read ψ) (NA σ) (SC σ))])

(define-extended-language etaPsi2Lang coreLang
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ))])

(define-extended-language etaPsi2SCLang coreLang
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ) (SC σ))])

(define-extended-language postReadLang coreLang
  [auxξ (η (Read ψ) (RelFront χ-tree) (NA σ) (P φ) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language etaPsi2SCpostLang coreLang
  [auxξ (η (Read ψ) (AcqFront ψ) (RelFront χ-tree) (NA σ) (Write ψ) (SC σ) (P φ) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-extended-language etaPsiGraphLang coreLang
  [auxξ (η (Read ψ) (NA σ) (Graph G) (GFront GF))])

(define-term etaPsiDefaultState (() (Read ()) (NA ())))

(define etaPsiCoreStep
  (extend-reduction-relation
    (define-coreStep etaPsiDefaultState)
   etaPsiLang #:domain ξ))
(define etaPsiCoreTest (define-coreTest etaPsiCoreStep etaPsiDefaultState))

(define-term postponedReadDefaultState (() (Read ()) (RelFront ()) (NA ()) (P ()) (R ()) (RW ()) (Deallocated ())))
(define postponedReadCoreStep
  (extend-reduction-relation
   (define-coreStep postponedReadDefaultState)
   postReadLang #:domain ξ))
(define postponedReadCoreTest (define-coreTest postponedReadCoreStep postponedReadDefaultState))

