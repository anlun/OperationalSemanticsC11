#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "etaPsiLang.rkt")
(provide define-naRules define-naReadRules define-naWriteStuckRules)


(define-syntax-rule (define-naReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (read   na ι)) auxξ)
        ((in-hole E (ret μ-value)) auxξ)
        "read-na"
        (where η       (getη     auxξ))
        (where ψ       (getReadψ auxξ))
        (where σ_read  (getByPath (pathE E) ψ))
        (where τ       (getLastTimestamp ι η))
        (where μ-value (getValueByCorrectTimestamp ι τ η))
        
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (nonNegativeτ τ))))
)))

(define-syntax-rule (define-naWriteStuckRules lang defaultState getWriteσ ιNotInReadQueue)
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

   (--> ((in-hole E (write na ι μ-value)) auxξ    )
        ((in-hole E (ret 0))              auxξ_new)
        "write-na"
        (where η      (getη     auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))
        
        (where τ       (getNextTimestamp ι η))
        (where ψ_new   (updateByFront path ((ι τ)) ψ))

        (where auxξ_upd_front (updateState (Read ψ) (Read ψ_new) auxξ))
        (where σ_write        (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new          (updateCell  ι μ-value σ_write η))
        (where auxξ_new       (updateState η η_new auxξ_upd_front))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (ιNotInReadQueue ι path auxξ))))
)))

(define-syntax-rule (define-naRules lang defaultState getWriteσ ιNotInReadQueue)
  (begin

  (union-reduction-relations
   (define-naReadRules lang)
   (define-naWriteStuckRules lang defaultState getWriteσ ιNotInReadQueue))
))

(define naRules
  (define-naRules etaPsiLang defaultState getWriteσ_nil ιNotInReadQueue_t))

(define naStep
  (union-reduction-relations coreStep naRules))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(define testTerm2
        (term ((spw
                   ((write na "x" 1) >>= (λ x (ret 1)))
                   ((write na "x" 2) >>= (λ x (ret 2))))
                  >>=
                  (λ x (ret x)))))

(test-->>∃ naStep
          (term (,testTerm2 defaultState))
          (term (stuck defaultState)))