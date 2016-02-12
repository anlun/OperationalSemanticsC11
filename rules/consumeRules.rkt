#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-conReadRules)

;; DD -- data dependencies
(define-metafunction coreLang
  propagateDD : path σ-dd AST -> AST
  [(propagateDD () σ-dd ((ret μ-value) >>= (λ vName AST)))
   ((ret μ-value) >>= (λ vName (propagateDD_helpF σ-dd vName AST)))]
  
  [(propagateDD path σ-dd (AST_0 >>= (λ vName AST_1)))
   ((propagateDD path σ-dd AST_0) >>= (λ vName AST_1))]

  [(propagateDD path σ-dd (ret μ)) (ret μ)]

  [(propagateDD (L path) σ-dd (par AST_0 AST_1))
   (par (propagateDD path σ-dd AST_0) AST_1)]
  [(propagateDD (R path) σ-dd (par AST_0 AST_1))
   (par AST_0 (propagateDD path σ-dd AST_1))])

(define (propagateDD-tests)
  (test-equal (term (propagateDD (R ())
                                 ()
                                 ((par (ret 0)
                                       ((ret 0) >>=
                                        (λ r1 (read na r1)))) >>=
                                  (λ r0 (ret r0)))))
              '((par (ret 0) ((ret 0) >>= (λ r1 (readCon na r1 ()))))
                >>=
                (λ r0 (ret r0))) ))

(propagateDD-tests)

(define-syntax-rule (define-conReadRules lang addReadNode)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (read con ι)) auxξ) 
       (normalize
        ((propagateDD path σ-dd
          (in-hole E (ret μ-value))) auxξ_new))
        "read-con"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ-dd     (getDataDependencies ι σ η))
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read con ι μ-value) path auxξ_upd_ψ))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read))))

   (-->  ((in-hole E (readCon con ι σ-dd)) auxξ)
       (normalize
        ((propagateDD path (frontMerge σ-dd σ-dd_new)
          (in-hole E (ret μ-value))) auxξ_new))
        "readCon-con"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ-dd_new (getDataDependecies ι σ η))
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read con ι μ-value) path auxξ_upd_ψ))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ-dd)))))

   (-->  ((in-hole E (readCon acq ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-acq"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path σ ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read acq ι μ-value) path auxξ_upd_ψ))
        (where σ_read     (getByPath path ψ))

        (side-condition (term (correctτ τ ι
                                        (frontMerge σ_read σ-dd)))))

   (-->  ((in-hole E (readCon rlx ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-rlx"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read rlx ι μ-value) path auxξ_upd_ψ))
        (where σ_read     (getByPath path ψ))

        (side-condition (term (correctτ τ ι
                                        (frontMerge σ_read σ-dd)))))
   (-->  ((in-hole E (readCon na ι σ-dd)) auxξ)
        (normalize
         ((propagateDD path σ-dd
           (in-hole E (ret μ-value))) auxξ_new))
        "readCon-na"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where τ       (getLastTimestamp ι η))
        (where μ-value (getValueByCorrectTimestamp ι τ η))

        (where auxξ_upd_ψ (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))
        (where auxξ_new   (addReadNode τ (read na ι μ-value) path auxξ_upd_ψ))
        (where σ_read     (getByPath path ψ))

        (side-condition (term (seeLast ι η (frontMerge σ_read σ-dd))))
        (side-condition (term (nonNegativeτ τ))))

  
   (--> ((in-hole E (readCon RM ι σ-dd)) auxξ)
        (stuck defaultState)
        "readCon-na-stuck"
        (where path (pathE E))
        (where σ_read (getReadσ path auxξ))
        (where σ_na   (getσNA auxξ))

        (where τ_cur  (fromMaybe -1 (lookup ι (frontMerge σ_read σ-dd))))
        (where τ_na   (fromMaybe -1 (lookup ι σ_na)))
        (side-condition (or (< (term τ_cur) (term τ_na))
                            (term (negativeτ τ_cur)))))

)))

(define-syntax-rule (define-conSCReadRules lang
                      getReadσ updateReadσ
                      synchronizeWriteFront
                      isReadQueueEqualTo
                      addReadNode)
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
