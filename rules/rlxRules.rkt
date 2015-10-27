#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../langs/etaPsiLang.rkt")
(require "../tests/testTerms.rkt")
(provide define-rlxRules define-rlxReadRules define-rlxWriteRules)

(define-syntax-rule (define-rlxReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (read  rlx ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-rlx"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_new (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read)))))))

(define-syntax-rule (define-rlxWriteRules lang getWriteσ isReadQueueEqualTo ιNotInReadQueue)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (write rlx ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret 0))               auxξ_new))
        "write-rlx"
        (where η       (getη auxξ))
        (where ψ_read  (getReadψ auxξ))
        (where path    (pathE E))

        (where τ              (getNextTimestamp ι η))
        (where ψ_read_new     (updateByFront path ((ι τ)) ψ_read))
        (where auxξ_upd_front (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ_write    (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new      (updateCell ι μ-value σ_write η))
        (where auxξ_new   (updateState η η_new auxξ_upd_front))

        (side-condition (term (ιNotInReadQueue_t ι path auxξ))))

   (-->  ((in-hole E (cas SM rlx ι μ-value_expected μ-value)) auxξ)
        (normalize
         ((in-hole E (ret μ-value                          )) auxξ_new))
        "cas-fail-rlx"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_new (updateState (Read ψ_read) (Read (updateByFront path ((ι τ)) ψ_read)) auxξ))

        (where σ_read   (getReadσ path auxξ))
        (side-condition (equal? (term τ) (term (getLastTimestamp ι η))))
        ;(side-condition (term (correctτ τ ι σ_read))) ; <- Previous condition implies it.
        (side-condition (not (equal? (term μ-value)
                                     (term μ-value_expected))))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
   
   (-->  ((in-hole E (cas rlx FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                     )) auxξ_new))
        "cas-succ-rlx"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))

        (where τ             (getNextTimestamp ι η))
        (where ψ_read_new    (updateByFront path ((ι τ)) ψ_read))
        (where auxξ_upd_read (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ_write    (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new      (updateCell  ι μ-value σ_write η))
        (where auxξ_new   (updateState η η_new auxξ_upd_read))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rlx FM)))
        (side-condition (term (ιNotInReadQueue ι path auxξ)))))))

(define-syntax-rule (define-rlxRules lang getWriteσ isReadQueueEqualTo_t ιNotInReadQueue)
  (begin

  (union-reduction-relations
   (define-rlxReadRules lang)
   (define-rlxWriteRules lang getWriteσ isReadQueueEqualTo ιNotInReadQueue))))
