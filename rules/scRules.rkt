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

(define-term defaultState (() (SC ())))

(define-metafunction scLang
  spwST : path auxξ -> auxξ
  [(spwST path auxξ) auxξ])

(define-metafunction scLang
  joinST : path auxξ -> auxξ
  [(joinST path auxξ) auxξ])

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t)
   scLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define-syntax-rule (define-scRules lang getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo)
  (begin
  
  (reduction-relation
   lang #:domain ξ

   (-->  ((in-hole E (write sc ι μ-value)) auxξ)
        (normalize
         ((in-hole E (ret μ-value))        auxξ_new))
        "write-sc"
        (where η      (getη   auxξ))
        (where τ      (getNextTimestamp ι η))
        (where σ_sc   (getσSC auxξ))
        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        (where σ_new  (updateFront ι τ (frontMerge σ_sc σ_read)))
        
        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_new) auxξ))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ_upd_sc))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where η_new          (updateCell  ι μ-value σ_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_write))

        (side-condition (term (isReadQueueEqualTo () path auxξ))))
      
   (-->  ((in-hole E (read   sc ι)) auxξ)
        (normalize
         ((in-hole E (ret μ-value)) auxξ_new))
        "read-sc"
        (where η (getη auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where σ_sc   (getσSC auxξ))
        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        
        (where σ_with_sc      (frontMerge σ_read σ_sc))
        (where σ_new          (frontMerge σ_with_sc σ))
        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_new) auxξ))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ_upd_sc))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where auxξ_new       auxξ_upd_write)
        
        (side-condition (term (correctτ τ ι σ_with_sc)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (-->  ((in-hole E (cas SM sc ι μ-value_expected μ-value)) auxξ)
        (normalize
         ((in-hole E (ret 0                               )) auxξ_new))
        "cas-fail-sc"
        (where η      (getη auxξ))
        (where σ_sc   (getσSC auxξ))
        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))

        (where τ              (getLastTimestamp ι η))
        (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ η)))
        (where σ_read_sync    (frontMerge σ_read σ_record_front))
        (where σ_new          (frontMerge σ_read_sync σ_sc))
        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_new) auxξ))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ_upd_sc))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where auxξ_new       auxξ_upd_write)

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM sc)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (-->  ((in-hole E (cas sc FM ι μ-value_expected μ-value_new)) auxξ)
        (normalize
         ((in-hole E (ret 1                                   )) auxξ_new))
        "cas-succ-sc"
        (where η      (getη auxξ))
        (where σ_sc   (getσSC auxξ))
        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        
        (where τ_last         (getLastTimestamp ι η))
        (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ_last η)))
        (where σ_with_sc      (frontMerge σ_sc σ_record_front))
        (where τ              (getNextTimestamp ι η))
        (where σ_new          (updateFront ι τ (frontMerge σ_read σ_with_sc)))
        (where auxξ_upd_sc    (updateState (SC σ_sc) (SC σ_new) auxξ))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ_upd_sc))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))

        (where η_new          (updateCell ι μ-value_new σ_new η))
        (where auxξ_new       (updateState η η_new auxξ_upd_write))

        (side-condition
         (term (succCAScondition ι η μ-value_expected sc FM)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
)
  ))

(define-metafunction scLang
  getReadσ_emp : path auxξ -> σ
  [(getReadσ_emp path auxξ) ()])

(define-metafunction scLang
  updateReadσ_id : path σ auxξ -> auxξ
  [(updateReadσ_id path σ auxξ) auxξ])

(define scRules (define-scRules scLang getReadσ_emp updateReadσ_id synchronizeWriteFront_id isReadQueueEqualTo_t))
