#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")
(provide define-scRules)

(define-syntax-rule (define-scRules lang)
  (begin
  
  (reduction-relation
   lang #:domain ξ

   (--> ((in-hole E (fence sc)) auxξ)
        ((in-hole E (ret 0    )) auxξ_new)
        "fence-sc"

        (where path     (pathE E))
        (side-condition (term (is-α-empty path auxξ)))

        (where auxξ_acq (synchronizeCurAcqFronts     path auxξ    ))
        (where auxξ_rel (synchronizeCurReleaseFronts path auxξ_acq))

        (where σ_sc        (getσSC auxξ))
        (where σ           (getByPath path (getReadσ-tree auxξ_rel)))
        (where auxξ_read_σ-tree (updateReadσ path σ_sc auxξ_rel))
        (where auxξ_new    (updateState (SC σ_sc) (SC (frontMerge σ σ_sc)) auxξ_read_σ-tree)))

   (-->  ((in-hole E (write sc ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret μ-value))        auxξ_new))
        "write-sc"
        (where η          (getη   auxξ))
        (where τ          (getNextTimestamp ι η))
        (where path       (pathE E))
        (where σ_read     (getReadσ path auxξ))
        (where σ_read_new (updateFront ι τ σ_read))
        (where σ_sc       (getσSC auxξ))
        (where σ_sc_new   (updateFront ι τ σ_sc))

        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_sc_new) auxξ))
        (where auxξ_upd_read  (updateReadσ path σ_read_new auxξ_upd_sc))
        (where auxξ_upd_acq   (updateAcqFront path ((ι τ)) auxξ_upd_read))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))
        (where η_new          (updateCell  ι μ-value σ_read_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_upd_γ     (add-γ-entries path ι τ auxξ_upd_η))
        (where auxξ_upd_γ_2   (addObservedWritesToγ path ι τ sc auxξ_upd_γ))
        (where auxξ_new       auxξ_upd_γ_2)

        ;(side-condition (term (is-α-empty path auxξ))))
        (side-condition (term (are-thread-post-insts-rlx  path auxξ)))
        (side-condition (term (ι-not-in-α-tree ι path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))
      
   (-->  ((in-hole E (read   sc ι σ-dd)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-sc"
        (where η    (getη auxξ))
        (where path (pathE E))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where σ_read   (getReadσ path auxξ))
        (where σ_sc     (getσSC auxξ))
        (side-condition (term (correctτ τ ι (frontMerge (frontMerge σ-dd σ_read) σ_sc))))

        (where σ_delta         (frontMerge ((ι τ)) σ))
        (where σ-tree_read     (getReadσ-tree auxξ))
        (where σ-tree_read_new (updateByFront path σ_delta σ-tree_read))
        (where auxξ_upd_read   (updateState (Read σ-tree_read) (Read σ-tree_read_new) auxξ))
        (where auxξ_upd_acq    (updateAcqFront path σ_delta auxξ_upd_read))
        
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))
        (where auxξ_new       auxξ_upd_write)
        
        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))

   (-->  ((in-hole E (cas SM sc ι μ-value_expected μ-value_new σ-dd)) auxξ)
        (normalize
         ((in-hole E (ret μ-value                                  )) auxξ_new))
        "cas-fail-sc"
        (where η (getη auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))

        (where σ_delta        (frontMerge σ_read σ))
        (where σ_new          (updateFront ι τ σ_delta))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ))
        (where auxξ_upd_acq   (updateAcqFront path σ_delta auxξ_upd_read))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))
        (where auxξ_new       auxξ_upd_write)
        
        (where σ_sc     (getσSC auxξ))
        ;; TODO: Why doesn't it read from the latest store to the location?
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ_sc))))
        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        (side-condition (not (equal? (term μ-value) (term μ-value_expected)))))

   (-->  ((in-hole E (cas sc FM ι μ-value_expected μ-value_new σ-dd)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                         )) auxξ_new))
        "cas-succ-sc"
        (where η          (getη     auxξ))
        (where σ-tree     (getReadσ-tree auxξ))
        (where path       (pathE E))
        (where τ          (getNextTimestamp ι η))
        (where σ_new      (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where σ-tree_new (updateByFront path σ_new σ-tree))

        (where σ_sc       (getσSC auxξ))
        (where σ_sc_new   (updateFront ι τ σ_sc))

        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_sc_new) auxξ))
        (where auxξ_upd_read  (updateState (Read σ-tree) (Read σ-tree_new) auxξ_upd_sc))
        (where auxξ_upd_acq   (updateAcqFront path σ_new auxξ_upd_read))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_acq))

        (where σ_new          (getByPath path σ-tree_new))
        (where η_new          (updateCell ι μ-value_new σ_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))

        (where auxξ_upd_γ   (addObservedWritesToγ path ι τ sc auxξ_upd_η))

        (where τ_last     (getLastTimestamp ι η))
        (where τ          (getNextTimestamp ι η))
        (where auxξ_new       (addReadNode τ_last
                                           (rmw sc ι μ-value_expected μ-value_new τ)
                                           path auxξ_upd_γ)) 
        
        (side-condition
         (term (succCAScondition ι η μ-value_expected sc FM)))
        (side-condition (term (is-α-empty path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ)))))
)))
