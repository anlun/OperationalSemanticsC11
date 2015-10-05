#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../langs/etaPsiLang.rkt")
(require "../tests/testTerms.rkt")
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

(define-syntax-rule (define-acqReadRules lang addReadNode addSWedges)
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (read  acq ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-acq"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_front (updateState (Read ψ) (Read (updateByFront path σ ψ)) auxξ))
        (where (number_node auxξ_with_node)
               (addReadNode τ (read acq ι μ-value) (pathE E) auxξ_upd_front))
        (where auxξ_new       (addSWedges number_node auxξ_with_node))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read))))
)))

(define-syntax-rule (define-relAcqWriteRules lang
                      synchronizeWriteFront isReadQueueEqualTo
                      ; TODO -> addReadNode -- add for fail    CAS
                      ; TODO -> addRMWNode  -- add for success CAS
                      addWriteNode)
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (write rel ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret 0))               auxξ_new))
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
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_new       (addWriteNode (write rel ι μ-value τ) path auxξ_upd_η))

        (side-condition (term (isReadQueueEqualTo () path auxξ))))
   
   (-->  ((in-hole E (cas SM acq ι μ-value_expected μ-value)) auxξ)
        (normalize
         ((in-hole E (ret 0                                )) auxξ_new))
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

   (-->  ((in-hole E (cas rel FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret 1                                    )) auxξ_new))
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

   (-->  ((in-hole E (cas acq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret 1                                    )) auxξ_new))
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

   (-->  ((in-hole E (cas relAcq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret 1                                       )) auxξ_new))
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

(define-syntax-rule (define-relAcqRules lang
                      addReadNode addSWedges
                      synchronizeWriteFront isReadQueueEqualTo
                      addWriteNode)
  (begin

  (union-reduction-relations
   (define-acqReadRules lang addReadNode addSWedges)
   (define-relAcqWriteRules lang synchronizeWriteFront isReadQueueEqualTo addWriteNode))
))

(define relAcqRules
  (define-relAcqRules etaPsiLang addReadNode_t addSWedges_t
    synchronizeWriteFront_id isReadQueueEqualTo_t addWriteNode_t))
(define step
  (union-reduction-relations coreStep relAcqRules))

#|
y_rel  = 1 || x_rel = 1
R1 = x_acq || R2 = y_acq

Can lead to R1 = R2 = 0.
|#
(test-->>∃ step
          (term (,testTerm1 defaultState))
          (term ((ret (0 0)) defaultState)))
