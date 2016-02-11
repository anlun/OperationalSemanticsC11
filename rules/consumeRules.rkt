#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(provide define-conReadRules)

(define-metafunction coreLang
  getDataDependencies_full : μ-value σ η -> σ-dd
  [(getDataDependencies_full ι σ η) ,(cons (term (ι τ))
                                            (term (getDataDependencies_full μ-value σ η)))
                                     (where (Just τ      ) (lookup ι σ))
                                     (where (Just μ-value) (getValueByTimestamp ι τ η))]
  [(getDataDependencies_full μ-value σ η) ()])

(define-metafunction coreLang
  getDataDependencies : μ-value σ η -> σ-dd
  [(getDataDependencies μ-value σ η) ,(cdr
                                       (term (getDataDependencies_full μ-value σ η)))])

(define (getDD-tests)
  (test-equal (term (getDataDependencies "x"
                                   (("x" 1) ("y" 1) ("z" 1))
                                   (("x" ((0 0 ()) (1 "y" ())))
                                    ("y" ((0 0 ()) (1 "z" ())))
                                    ("z" ((0 0 ()) (1  1  ()))))))
              (term (("y" 1) ("z" 1))))

  (test-equal (term (getDataDependencies "p"
                                         (("data" 0) ("p" 0))
                                         (("data" ((1 5 (("data" 1))) (0 0 (("data" 0)))))
                                          ("p"
                                           ((1 "data" (("data" 1) ("p" 1)))
                                            (0 0 (("data" 0) ("p" 0))))))))
              (term ()))

  (test-equal (term (getDataDependencies "p"
                                         (("data" 1) ("p" 1))
                                         (("data" ((1 5 (("data" 1))) (0 0 (("data" 0)))))
                                          ("p"
                                           ((1 "data" (("data" 1) ("p" 1)))
                                            (0 0 (("data" 0) ("p" 0))))))))
              (term (("data" 1)))))
(getDD-tests)

(define-metafunction coreLang
  propagateDD_helpF : σ-dd vName AST -> AST

  [(propagateDD_helpF σ-dd vName (read RM vName))
   (readCon RM vName σ-dd)]

  [(propagateDD_helpF σ-dd vName (cas SM FM vName μ_0 μ_1))
   (casCon SM FM vName μ_0 μ_1 σ-dd)]

  [(propagateDD_helpF σ-dd vName (if Expr AST_0 AST_1))
   (if Expr
       (propagateDD_helpF σ-dd vName AST_0)
       (propagateDD_helpF σ-dd vName AST_1))]

  [(propagateDD_helpF σ-dd vName (repeat AST))
   (repeat
       (propagateDD_helpF σ-dd vName AST))]

  [(propagateDD_helpF σ-dd vName_0 (AST_0 >>= (λ vName AST_1)))
   ((propagateDD_helpF σ-dd vName_0 AST_0) >>=
    (λ vName_0 (propagateDD_helpF σ-dd vName_0 AST_1)))   
   (side-condition (not (equal? (term vName_0) (term vName_1))))]

  [(propagateDD_helpF σ-dd vName (AST_0 >>= (λ vName AST_1)))
   ((propagateDD_helpF σ-dd vName AST_0) >>=
    (λ vName AST_1))]
  
  [(propagateDD_helpF σ-dd vName AST) AST])

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

;; (propagateDD (R ()) () ((par ((write na "data" 5) >>= (λ r-1 (write rel "p" "data"))) ((ret 0) >>= (λ r1 (if (!= r1 0) (read na r1) (ret 1))))) >>= (λ r0 (ret (proj2 r0)))))


(define-syntax-rule (define-conReadRules lang addReadNode)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (-->  ((in-hole E (read  con ι)) auxξ) 
        ;; (normalize
         ;; ((in-hole E (ret μ-value)) auxξ_new))
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
