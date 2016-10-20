#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")
(provide define-conReadRules)

(define-syntax-rule (define-conReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (read con ι)) auxξ) 
       (normalize
        ((propagateDD path σ-dd
          (in-hole E (ret μ-value))) auxξ_new))
        "read-con"
        (where η      (getη auxξ))
        (where σ-tree      (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ-dd     (getDataDependencies ι σ η))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path ((ι τ)) σ-tree)) auxξ))
        (where auxξ_new   (addReadNode τ (read con ι μ-value) path auxξ_upd_σ-tree))

        (where σ_read   (getByPath path σ-tree))
        (side-condition (term (correctτ τ ι σ_read)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (readCon con ι σ-dd)) auxξ)
       (normalize
        ((propagateDD path (frontMerge σ-dd σ-dd_new)
          (in-hole E (ret μ-value))) auxξ_new))
        "readCon-con"
        (where η      (getη auxξ))
        (where σ-tree      (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ-dd_new (getDataDependecies ι σ η))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path ((ι τ)) σ-tree)) auxξ))
        (where auxξ_new   (addReadNode τ (read con ι μ-value) path auxξ_upd_σ-tree))

        (where σ_read   (getByPath path σ-tree))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ-dd))))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (readCon acq ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-acq"
        (where η      (getη auxξ))
        (where σ-tree      (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path σ σ-tree)) auxξ))
        (where auxξ_new   (addReadNode τ (read acq ι μ-value) path auxξ_upd_σ-tree))
        (where σ_read     (getByPath path σ-tree))

        (side-condition (term (correctτ τ ι
                                        (frontMerge σ_read σ-dd))))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (readCon rlx ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-rlx"
        (where η      (getη auxξ))
        (where σ-tree      (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path ((ι τ)) σ-tree)) auxξ))
        (where auxξ_new   (addReadNode τ (read rlx ι μ-value) path auxξ_upd_σ-tree))
        (where σ_read     (getByPath path σ-tree))

        (side-condition (term (correctτ τ ι
                                        (frontMerge σ_read σ-dd))))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (readCon na ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-na"
        (where η      (getη auxξ))
        (where σ-tree      (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where τ       (getLastTimestamp ι η))
        (where μ-value (getValueByCorrectTimestamp ι τ η))

        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path ((ι τ)) σ-tree)) auxξ))
        (where auxξ_new   (addReadNode τ (read na ι μ-value) path auxξ_upd_σ-tree))
        (where σ_read     (getByPath path σ-tree))

        (side-condition (term (seeLast ι η (frontMerge σ_read σ-dd))))
        (side-condition (term (nonNegativeτ τ)))
        (side-condition (term (isPossibleE E auxξ))))

  
   (--> ((in-hole E (readCon RM ι σ-dd)) auxξ)
        (stuck defaultState)
        "readCon-na-stuck"
        (where path (pathE E))
        (where σ_read (getReadσ path auxξ))
        (where σ_na   (getσNA auxξ))

        (where τ_cur  (fromMaybe -1 (lookup ι (frontMerge σ_read σ-dd))))
        (where τ_na   (fromMaybe -1 (lookup ι σ_na)))
        (side-condition (or (< (term τ_cur) (term τ_na))
                            (term (negativeτ τ_cur))))
        (side-condition (term (isPossibleE E auxξ))))

)))

(define-syntax-rule (define-conSCReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ
 
   (-->  ((in-hole E (readCon sc ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-sc"
        (where η (getη auxξ))
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where path   (pathE E))
        (where σ_read (getReadσ path auxξ))
        
        (where σ_new          (updateFront ι τ (frontMerge σ_read σ)))
        (where auxξ_upd_read  (updateReadσ path σ_new auxξ))
        (where auxξ_upd_write (synchronizeWriteFront path auxξ_upd_read))
        (where auxξ_new       (addReadNode τ (read sc ι μ-value) path auxξ_upd_write))
        
        (where σ_sc     (getσSC auxξ))
        (side-condition (term (correctτ τ ι 
                                        ((frontMerge σ_read σ_sc) σ-dd))))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))
)))
