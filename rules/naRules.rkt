#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../langs/etaPsiLang.rkt")
(require "../tests/testTerms.rkt")
(provide define-naRules define-naReadRules define-naWriteStuckRules)

(define-syntax-rule (define-naReadRules lang addReadNode)
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (read   na ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-na"
        (where η       (getη     auxξ))
        (where ψ       (getReadψ auxξ))
        (where σ_read  (getByPath (pathE E) ψ))
        (where τ       (getLastTimestamp ι η))
        (where μ-value (getValueByCorrectTimestamp ι τ η))

        (where path (pathE E))
        (where auxξ_new (addReadNode τ (read na ι μ-value) path auxξ))
        
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (nonNegativeτ τ))))
)))

(define-syntax-rule (define-naWriteStuckRules lang
                      defaultState getWriteσ ιNotInReadQueue addWriteNode)
  (begin

  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (write na ι μ-value)) auxξ)
        (stuck defaultState)
        "write-na-stuck"
        (where η        (getη     auxξ))
        (where ψ        (getReadψ auxξ))
        (where σ_read   (getByPath (pathE E) ψ))
        (side-condition (term (dontSeeLast ι η σ_read))))
   
   (--> ((in-hole E (read na ι)) auxξ)
        (stuck defaultState)
        "read-na-stuck"
        (where η      (getη     auxξ))
        (where ψ      (getReadψ auxξ))
        (where σ_read (getByPath (pathE E) ψ))
        (side-condition
         (or (term (dontSeeLast ι η σ_read))
             (term (negativeτ (getLastTimestamp ι η))))))

   (-->  ((in-hole E (write na ι μ-value)) auxξ    )
        (normalize
         ((in-hole E (ret 0))              auxξ_new))
        "write-na"
        (where η      (getη     auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))
        
        (where τ       (getNextTimestamp ι η))
        (where ψ_new   (updateByFront path ((ι τ)) ψ))

        (where auxξ_upd_front (updateState (Read ψ) (Read ψ_new) auxξ))
        (where σ_write        (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new          (updateCell  ι μ-value σ_write η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_front))
        (where auxξ_new       (addWriteNode (write na ι μ-value τ) path auxξ_upd_η))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (ιNotInReadQueue ι path auxξ))))
)))

(define-syntax-rule (define-naRules lang
                      addReadNode defaultState getWriteσ ιNotInReadQueue addWriteNode)
  (begin

  (union-reduction-relations
   (define-naReadRules lang addReadNode)
   (define-naWriteStuckRules lang defaultState getWriteσ ιNotInReadQueue addWriteNode))
))

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