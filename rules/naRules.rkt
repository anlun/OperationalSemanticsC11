#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
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
        (side-condition (term (nonNegativeτ τ)))))))

(define-syntax-rule (define-naWriteStuckRules lang
                      defaultState getWriteσ ιNotInReadQueue addWriteNode)
  (begin

  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (write WM ι μ-value)) auxξ)
        (stuck defaultState)
        "write-na-stuck"
        (where path (pathE E))
        (where σ_read (getReadσ path auxξ))
        (where σ_na   (getσNA auxξ))

        (where τ_cur  (fromMaybe  0 (lookup ι σ_read)))
        (where τ_na   (fromMaybe -1 (lookup ι σ_na)))
        (side-condition (< (term τ_cur) (term τ_na))))
        #|
        (where η        (getη     auxξ))
        (where ψ        (getReadψ auxξ))
        (where σ_read   (getByPath (pathE E) ψ))
        (side-condition (term (dontSeeLast ι η σ_read)))
        |#
   
   (--> ((in-hole E (read RM ι)) auxξ)
        (stuck defaultState)
        "read-na-stuck"
        (where path (pathE E))
        (where σ_read (getReadσ path auxξ))
        (where σ_na   (getσNA auxξ))

        (where τ_cur  (fromMaybe -1 (lookup ι σ_read)))
        (where τ_na   (fromMaybe -1 (lookup ι σ_na)))
        (side-condition (or (< (term τ_cur) (term τ_na))
                            (term (negativeτ τ_cur)))))
        #|
        (where η      (getη     auxξ))
        (where ψ      (getReadψ auxξ))
        (where σ_read (getByPath (pathE E) ψ))
        (side-condition
         (or (term (dontSeeLast ι η σ_read))
             (term (negativeτ (getLastTimestamp ι η)))))
        |#

#|
Reading from NA write can't give any information, because a thread executing
a corresponding read action should be acknowledged (Wna happens-before R) about the NA
record (so as about a synchronization front stored in it).
|#
   (-->  ((in-hole E (write na ι μ-value)) auxξ    )
        (normalize
         ((in-hole E (ret μ-value))        auxξ_new))
        "write-na"
        (where η      (getη     auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))
        
        (where τ       (getNextTimestamp ι η))
        (where ψ_new   (updateByFront path ((ι τ)) ψ))

        (where auxξ_upd_front (updateState (Read ψ) (Read ψ_new) auxξ))
        (where η_new          (updateCell  ι μ-value ((ι τ)) η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_front))

        (where σ_na           (getσNA auxξ))
        (where σ_na_new       (updateFront ι τ σ_na))
        (where auxξ_upd_na    (updateState (NA σ_na) (NA σ_na_new) auxξ_upd_η))

        (where auxξ_new       (addWriteNode (write na ι μ-value τ) path auxξ_upd_na))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (ιNotInReadQueue ι path auxξ)))))))

(define-syntax-rule (define-naRules lang
                      addReadNode defaultState getWriteσ ιNotInReadQueue addWriteNode)
  (begin

  (union-reduction-relations
   (define-naReadRules lang addReadNode)
   (define-naWriteStuckRules lang defaultState getWriteσ ιNotInReadQueue addWriteNode))))
