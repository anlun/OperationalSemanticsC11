#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "etaPsiLang.rkt")
(provide define-relAcqRules define-acqReadRules define-relAcqWriteRules)

(define-metafunction coreLang
  acqFailCASσReadNew : ι η σ -> σ
  [(acqFailCASσReadNew ι η σ_read)
   (frontMerge σ_read σ_record_front)
   
   (where τ_last         (getLastTimestamp ι η))
   (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ_last η)))])

(define-metafunction coreLang
  acqSuccCASσReadNew : ι η σ -> σ
  [(acqSuccCASσReadNew ι η σ_read)
   (updateFront ι τ (acqFailCASσReadNew ι η σ_read))
   (where τ (getNextTimestamp ι η))])

(define-syntax-rule (define-acqReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (read  acq ι)) auxξ)
        ((in-hole E (ret μ-value)) auxξ_new)
        "read-acq"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_new (updateState (Read ψ) (Read (updateByFront path σ ψ)) auxξ))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read))))
)))

(define-syntax-rule (define-relAcqWriteRules lang synchronizeWriteFront isReadQueueEqualTo)
  (begin

  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (write rel ι μ-value)) auxξ)
        ((in-hole E (ret 0))               auxξ_new)
        "write-rel"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where τ       (getNextTimestamp ι η))
        (where σ_delta ((ι τ)))
        (where ψ_new   (updateByFront path σ_delta ψ))
        (where σ_new   (getByPath path ψ_new))

        (where auxξ_upd_read  (updateState (Read ψ) (Read ψ_new) auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where η_new          (updateCell ι μ-value σ_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_write))

        (side-condition (term (isReadQueueEqualTo () path auxξ))))
   
   (--> ((in-hole E (cas SM acq ι μ-value_expected μ-value)) auxξ)
        ((in-hole E (ret 0                                )) auxξ_new)
        "cas-fail-acq"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))

        (where σ_read_new (acqFailCASσReadNew ι η (getReadσ path auxξ)))
        (where ψ_read_new (updateByFront path σ_read_new ψ_read))
        (where auxξ_new   (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM acq)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (--> ((in-hole E (cas rel FM ι μ-value_expected μ-value_new)) auxξ)
        ((in-hole E (ret 1                                    )) auxξ_new)
        "cas-succ-rel"
        (where η          (getη     auxξ))
        (where ψ_read     (getReadψ auxξ))
        (where path       (pathE E))
        (where τ          (getNextTimestamp ι η))
        (where ψ_read_new (updateByFront path ((ι τ)) ψ_read))

        (where auxξ_upd_read  (updateState (Read ψ_read) (Read ψ_read_new) auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))

        (where σ_new          (getByPath path ψ_read_new))
        (where η_new          (updateCell ι μ-value_new σ_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_write))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rel FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (--> ((in-hole E (cas acq FM ι μ-value_expected μ-value_new)) auxξ)
        ((in-hole E (ret 1                                    )) auxξ_new)
        "cas-succ-acq"
        (where η       (getη     auxξ))
        (where ψ_read  (getReadψ auxξ))
        (where path    (pathE E))
        (where σ_read_new    (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where ψ_read_new    (updateByFront path σ_read_new ψ_read))
        (where auxξ_upd_read (updateState (Read ψ_read) (Read ψ_read_new) auxξ))
        ; Maybe we should update write front on this operation
        
        (where η_new          (updateCell  ι μ-value_new σ_read_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_read))
        (side-condition
         (term (succCAScondition ι η μ-value_expected acq FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (--> ((in-hole E (cas relAcq FM ι μ-value_expected μ-value_new)) auxξ)
        ((in-hole E (ret 1                                       )) auxξ_new)
        "cas-succ-relAcq"
        (where η          (getη     auxξ))
        (where ψ_read     (getReadψ auxξ))
        (where path       (pathE E))
        (where τ          (getNextTimestamp ι η))
        (where σ_read_new    (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where ψ_read_new    (updateByFront path σ_read_new ψ_read))

        (where auxξ_upd_read  (updateState (Read ψ_read) (Read ψ_new) auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))

        (where σ_new          (getByPath path ψ_read_new))
        (where η_new          (updateCell ι μ-value_new σ_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_write))

        (side-condition
         (term (succCAScondition ι η μ-value_expected relAcq FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
)))

(define-syntax-rule (define-relAcqRules lang synchronizeWriteFront isReadQueueEqualTo)
  (begin

  (union-reduction-relations
   (define-acqReadRules lang)
   (define-relAcqWriteRules lang synchronizeWriteFront isReadQueueEqualTo))
))

(define relAcqRules
  (define-relAcqRules etaPsiLang synchronizeWriteFront_id isReadQueueEqualTo_t))
(define step
  (union-reduction-relations coreStep relAcqRules))

#|
y_rel  = 1 || x_rel = 1
R1 = x_acq || R2 = y_acq

Can lead to R1 = R2 = 0.
|#
(define testTerm1
        (term ((spw
                   ((write rel "y" 1) >>= (λ x (
                    (read  acq "x")   >>= (λ x
                    (ret x)))))
                   ((write rel "x" 1) >>= (λ x (
                    (read  acq "y")   >>= (λ x
                    (ret x))))))
                  >>=
                  (λ x (ret x)))))

(define testTerm1-state
  (term (
         (("x" ((0 0 (("x" 0))))) ("y" ((0 0 (("y" 0))))))
         (Read (("x" 0) ("y" 0)))
         )))

(test-->>∃ step
          (term (,testTerm1 ,testTerm1-state))
          (term ((ret (0 0)) defaultState)))
