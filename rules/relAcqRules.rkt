#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-relAcqRules define-acqReadRules define-relAcqWriteRules)

(define-syntax-rule (define-acqReadRules lang addReadNode)
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
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path σ ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read acq ι μ-value) path auxξ_upd_ψ))
        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read)))
        (side-condition (term (isPossibleE E auxξ)))))))

(define-syntax-rule (define-relAcqWriteRules lang
                      addReadNode
                      synchronizeWriteFront isReadQueueEqualTo
                      are∀PostReadsRlx ιNotInReadQueue
                      ; TODO -> addRMWnode  -- add for success CAS
                      addWriteNode)
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (write rel ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret μ-value))         auxξ_new))
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
        (where η_new          (updateCell  ι μ-value σ_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_upd_γ     (addPostReadsToγ path ι τ auxξ_upd_η))
        (where auxξ_new       (addWriteNode (write rel ι μ-value τ) path auxξ_upd_γ))

        ;(side-condition (term (isReadQueueEqualTo () path auxξ))))
        (side-condition (term (are∀PostReadsRlx  path auxξ)))
        (side-condition (term (ιNotInReadQueue ι path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
   
   (-->  ((in-hole E (cas SM acq ι μ-value_expected μ-value_to_write)) auxξ)
        (normalize
         ((in-hole E (ret μ-value                                   )) auxξ_new))
        "cas-fail-acq"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path σ ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read acq ι μ-value) path auxξ_upd_ψ))

        (where σ_read   (getReadσ path auxξ))
        (side-condition (equal? (term τ) (term (getLastTimestamp ι η))))
        ;(side-condition (term (correctτ τ ι σ_read))) ; <- Previous condition implies it.
        (side-condition (not (equal? (term μ-value)
                                     (term μ-value_expected))))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
        
   (-->  ((in-hole E (cas rel FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                     )) auxξ_new))
        "cas-succ-rel"
        (where η          (getη     auxξ))
        (where ψ_read     (getReadψ auxξ))
        (where path       (pathE E))
        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where ψ_read_new (updateByFront path ((ι τ)) ψ_read))

        (where auxξ_upd_read  (updateState (Read ψ_read) (Read ψ_read_new) auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))

        (where σ_new          (getByPath path ψ_read_new))
        (where η_new          (updateCell  ι μ-value_new
                                           (acqSuccCASσReadNew ι η σ_new)
                                           η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw rel ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_η))
        (side-condition
         (term (succCAScondition ι η μ-value_expected rel FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
   
   (-->  ((in-hole E (cas acq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                     )) auxξ_new))
        "cas-succ-acq"
        (where η       (getη     auxξ))
        (where ψ_read  (getReadψ auxξ))
        (where path    (pathE E))
        (where σ_read_new    (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where ψ_read_new    (updateByFront path σ_read_new ψ_read))
        (where auxξ_upd_read (updateState (Read ψ_read) (Read ψ_read_new) auxξ))
        ; Maybe we should update write front on this operation
        
        (where η_new          (updateCell  ι μ-value_new σ_read_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_read))
        
        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw acq ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_η))
        
        (side-condition
         (term (succCAScondition ι η μ-value_expected acq FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (cas relAcq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                        )) auxξ_new))
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
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))

        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw relAcq ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_η))        
        
        (side-condition
         (term (succCAScondition ι η μ-value_expected relAcq FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ)))))))

(define-syntax-rule (define-relAcqRules lang
                      addReadNode
                      synchronizeWriteFront isReadQueueEqualTo
                      are∀PostReadsRlx ιNotInReadQueue
                      addWriteNode)
  (begin

  (union-reduction-relations
   (define-acqReadRules     lang addReadNode)
   (define-relAcqWriteRules lang addReadNode synchronizeWriteFront
     isReadQueueEqualTo are∀PostReadsRlx ιNotinReadQueue addWriteNode))))
