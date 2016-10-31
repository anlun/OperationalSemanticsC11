#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")
(provide define-relAcqRules define-acqReadRules define-relAcqWriteRules define-relAcqCasRules)

(define-syntax-rule (define-acqReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (read  acq ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-acq"
        (where η      (getη auxξ))
        (where σ-tree (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        
        (where σ-tree_new      (updateByFront path σ σ-tree))
        (where auxξ_upd_read   (updateState (Read σ-tree) (Read σ-tree_new) auxξ))
        (where auxξ_upd_acq    (updateAcqFront path σ auxξ_upd_read))
        (where auxξ_new        (addReadNode τ (read acq ι μ-value) path auxξ_upd_acq))

        (where σ_read (getByPath path σ-tree))
        (side-condition (term (correctτ τ ι σ_read)))))))

(define-syntax-rule (define-relWriteRules lang) 
  (begin

  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (write rel ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret μ-value))         auxξ_new))
        "write-rel"
        (where η      (getη auxξ))
        (where σ-tree (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where τ            (getNextTimestamp ι η))
        (where σ_delta      ((ι τ)))
        (where σ-tree_new   (updateByFront path σ_delta σ-tree))
        (where σ_new        (getByPath path σ-tree_new))

        (where auxξ_upd_read  (updateState (Read σ-tree) (Read σ-tree_new) auxξ))
        (where auxξ_upd_acq   (updateAcqFront path σ_delta auxξ_upd_read))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))
        (where η_new          (updateCell  ι μ-value σ_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_upd_γ     (addPostReadsToγ path ι τ auxξ_upd_η))
        (where auxξ_upd_γ_2   (addObservedWritesToγ path ι τ rel auxξ_upd_γ))
        (where auxξ_upd_χ     (updateRelFront path ι σ_new auxξ_upd_γ_2))
        (where auxξ_new       (addWriteNode (write rel ι μ-value τ) path auxξ_upd_χ))

        (side-condition (term (are∀PostReadsRlx  path auxξ)))
        (side-condition (term (ι-not-in-α-tree ι path auxξ)))))))

(define-syntax-rule (define-relAcqCasRules lang) 
  (begin

  (reduction-relation
   lang #:domain ξ


   (-->  ((in-hole E (cas SM acq ι μ-value_expected μ-value_to_write)) auxξ)
        (normalize
         ((in-hole E (ret μ-value                                   )) auxξ_new))
        "cas-fail-acq"
        (where η                          (getη auxξ))
        (where σ-tree                     (getReadσ-tree auxξ))
        (where path                       (pathE E))
        (where σ_read                     (getReadσ path auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where σ-tree_new      (updateByFront path σ σ-tree))
        (where auxξ_upd_read   (updateState (Read σ-tree) (Read σ-tree_new) auxξ))
        (where auxξ_upd_acq    (updateAcqFront path σ auxξ_upd_read))
        (where auxξ_new        (addReadNode τ (read acq ι μ-value) path auxξ_upd_acq))

        (side-condition (equal? (term τ) (term (getLastTimestamp ι η))))
        ;(side-condition (term (correctτ τ ι σ_read))) ; <- Previous condition implies it.
        (side-condition (not (equal? (term μ-value)
                                     (term μ-value_expected))))

        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (isRestrictedByγ_auxξ ι τ acq auxξ))))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))
        
   (-->  ((in-hole E (cas rel FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                     )) auxξ_new))
        "cas-succ-rel"
        (where η               (getη     auxξ))
        (where σ-tree_read     (getReadσ-tree auxξ))
        (where path            (pathE E))
        (where τ_last          (getLastTimestamp ι η))
        (where τ               (getNextTimestamp ι η))
        
        (where σ_delta         ((ι τ)))
        (where σ-tree_read_new (updateByFront path σ_delta σ-tree_read))
        (where auxξ_upd_read   (updateState (Read σ-tree_read) (Read σ-tree_read_new) auxξ))
        (where auxξ_upd_acq    (updateAcqFront path σ_delta auxξ_upd_read))
        (where auxξ_upd_write  (synchronizeWriteFront path auxξ_upd_acq))

        (where σ_new          (getByPath path σ-tree_read_new))
        (where η_new          (updateCell  ι μ-value_new
                                           (acqSuccCASσReadNew ι η σ_new)
                                           η))

        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_upd_γ     (addObservedWritesToγ path ι τ rel auxξ_upd_η))
        (where auxξ_upd_χ     (updateRelFront path ι σ_new auxξ_upd_γ))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw rel ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_χ))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rel FM)))

        (side-condition (term (is-α-empty path auxξ)))
        ;; (side-condition (not (term (isRestrictedByγ_auxξ ι τ rlx auxξ))))
        (side-condition (not (term (isRestrictedByγ_auxξ ι τ_last acq auxξ))))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))
   
   (-->  ((in-hole E (cas acq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                     )) auxξ_new))
        "cas-succ-acq"
        (where η            (getη     auxξ))
        (where σ-tree_read  (getReadσ-tree auxξ))
        (where path         (pathE E))

        (where σ_read_new         (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where σ-tree_read_new    (updateByFront path σ_read_new σ-tree_read))
        (where auxξ_upd_read      (updateState (Read σ-tree_read) (Read σ-tree_read_new) auxξ))
        (where auxξ_upd_acq       (updateAcqFront path σ_read_new auxξ_upd_read))
        ; Maybe we should update write front on this operation
        
        (where η_new          (updateCell  ι μ-value_new σ_read_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_acq))
        
        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw acq ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_η))
        
        (side-condition
         (term (succCAScondition ι η μ-value_expected acq FM)))
        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (isRestrictedByγ_auxξ ι τ_last acq auxξ))))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))

   (-->  ((in-hole E (cas relAcq FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                        )) auxξ_new))
        "cas-succ-relAcq"
        (where η               (getη     auxξ))
        (where σ-tree          (getReadσ-tree auxξ))
        (where path            (pathE E))
        (where τ               (getNextTimestamp ι η))
        (where σ_new           (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where σ-tree_new      (updateByFront path σ_new σ-tree))

        (where auxξ_upd_read  (updateState (Read σ-tree) (Read σ-tree_new) auxξ))
        (where auxξ_upd_acq   (updateAcqFront path σ_new auxξ_upd_read))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))

        (where σ_new          (getByPath path σ-tree_new))
        (where η_new          (updateCell ι μ-value_new σ_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))

        (where auxξ_upd_γ     (addObservedWritesToγ path ι τ rel auxξ_upd_η))
        (where auxξ_upd_χ     (updateRelFront path ι σ_new auxξ_upd_γ))

        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw relAcq ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_χ))        
        
        (side-condition
         (term (succCAScondition ι η μ-value_expected relAcq FM)))
        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (isRestrictedByγ_auxξ ι τ_last acq auxξ))))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))))))

(define-syntax-rule (define-relAcqWriteRules lang)
  (begin
    (union-reduction-relations
     (define-relWriteRules  lang)
     (define-relAcqCasRules lang))))

(define-syntax-rule (define-relAcqRules lang)
  (begin
    (union-reduction-relations
     (define-acqReadRules     lang)
     (define-relAcqWriteRules lang))))
