#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-scRules)

(define-extended-language scLang coreLang
  ; State:
  ; AST -- current state of program tree;
  ; η      -- current heap history;
  ; (SC σ) -- front after last SC operation;
  ; θ      -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (SC σ) θ ...)])

(define-syntax-rule (define-scRules lang getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo are∀postReadsRlx ιNotInReadQueue)
  (begin
  
  (reduction-relation
   lang #:domain ξ


   (--> ((in-hole E (fence sc)) auxξ)
        ((in-hole E (ret 0    )) auxξ_new)
        "fence-sc"

        (where path     (pathE E))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))

        (where auxξ_acq (synchronizeCurAcqFronts     path auxξ    ))
        (where auxξ_rel (synchronizeCurReleaseFronts path auxξ_acq))

        (where σ_sc        (getσSC auxξ))
        (where σ           (getByPath path (getReadψ auxξ_rel)))
        (where auxξ_read_ψ (updateReadσ path σ_sc auxξ_rel))
        (where auxξ_new    (updateState (SC σ_sc) (SC (frontMerge σ σ_sc)) auxξ_read_ψ)))

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
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where η_new          (updateCell  ι μ-value σ_read_new η))
        (where auxξ_upd_η     (updateState η η_new auxξ_upd_write))
        (where auxξ_upd_γ     (addPostReadsToγ path ι τ auxξ_upd_η))
        (where auxξ_upd_γ_2   (addObservedWritesToγ path ι τ sc auxξ_upd_γ))
        (where auxξ_new       auxξ_upd_γ_2)

        ;(side-condition (term (isReadQueueEqualTo () path auxξ))))
        (side-condition (term (are∀PostReadsRlx  path auxξ)))
        (side-condition (term (ιNotInReadQueue ι path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        (side-condition (term (isPossibleE E auxξ))))
      
   (-->  ((in-hole E (read   sc ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-sc"
        (where η (getη auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        
        (where σ_new          (updateFront ι τ (frontMerge σ_read σ)))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where auxξ_new       auxξ_upd_write)
        
        (where σ_sc     (getσSC auxξ))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ_sc))))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (cas SM sc ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value                             )) auxξ_new))
        "cas-fail-sc"
        (where η (getη auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        
        (where σ_new          (updateFront ι τ (frontMerge σ_read σ)))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where auxξ_new       auxξ_upd_write)
        
        (where σ_sc     (getσSC auxξ))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ_sc))))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        (side-condition (not (equal? (term μ-value) (term μ-value_expected))))

        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (cas sc FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret μ-value_expected                    )) auxξ_new))
        "cas-succ-sc"
        (where η          (getη     auxξ))
        (where ψ_read     (getReadψ auxξ))
        (where path       (pathE E))
        (where τ          (getNextTimestamp ι η))
        (where σ_read_new    (acqSuccCASσReadNew ι η (getReadσ path auxξ)))
        (where ψ_read_new    (updateByFront path σ_read_new ψ_read))

        (where σ_sc       (getσSC auxξ))
        (where σ_sc_new   (updateFront ι τ σ_sc))

        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_sc_new) auxξ))
        (where auxξ_upd_read  (updateState (Read ψ_read) (Read ψ_new) auxξ_sc))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))

        (where σ_new          (getByPath path ψ_read_new))
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
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (not (term (hasιInObservedWrites path ι auxξ))))
        (side-condition (term (isPossibleE E auxξ)))))))
