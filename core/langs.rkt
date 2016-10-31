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
; (Read     σ-tree)     -- per-thread read    fronts;
; (AcqFront σ-tree)     -- per-thread acquire fronts;
; (RelFront χ-tree)     -- per-thread release fronts;
; (NA       σ     )     -- location -> last NA write on it;
; (Write    σ-tree)     -- current threads write fronts;
; (SC       σ     )     -- front after last SC operation.
; (P        α-tree)     -- component with thread-specific information about postponed reads;
; (R        γ     )     -- component with restiction on a resolve order for postponed reads;
; (RW observedWrites)   -- (path, ι) -> observed uncommitted to history writes.

; (Graph  G )           -- current graph of memory actions;
; (GFront GF)           -- thread positions in the graph.

(define-extended-language etaPsiLang coreLang
  [auxξ (η (Read σ-tree) (NA σ))])

(define-extended-language etaPsiSCLang coreLang
  [auxξ (η (Read σ-tree) (NA σ) (SC σ))])

(define-extended-language etaPsi2Lang coreLang
  [auxξ (η (Read σ-tree) (AcqFront σ-tree) (RelFront χ-tree) (NA σ) (Write σ-tree))])

(define-extended-language etaPsi2SCLang coreLang
  [auxξ (η (Read σ-tree) (AcqFront σ-tree) (RelFront χ-tree) (NA σ) (Write σ-tree) (SC σ))])

(define-extended-language postReadLang coreLang
  [auxξ (η (Read σ-tree) (RelFront χ-tree) (NA σ) (P α-tree) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language etaPsi2SCpostLang coreLang
  [auxξ (η (Read σ-tree) (AcqFront σ-tree) (RelFront χ-tree) (NA σ) (Write σ-tree) (SC σ) (P α-tree) (R γ) (RW observedWrites) (Deallocated listι))])

(define-extended-language graphLang coreLang
  [auxξ (η (Graph G) (GFront GF))])

(define-extended-language etaPsiGraphLang coreLang
  [auxξ (η (Read σ-tree) (NA σ) (Graph G) (GFront GF))])

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

