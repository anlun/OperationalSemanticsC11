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
   
   (-->  ((in-hole E (read con ι σ-dd)) auxξ)
       (normalize
        ((propagateDD path (frontMerge σ-dd σ-dd_new)
          (in-hole E (ret μ-value))) auxξ_new))
        "read-con"
        (where η      (getη auxξ))
        (where σ-tree (getReadσ-tree auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))

        (where σ_read   (getByPath path σ-tree))
        (side-condition (term (correctτ τ ι (frontMerge σ_read σ-dd))))

        (where σ-dd_new        (getDataDependencies ι σ η))
        (where auxξ_upd_σ-tree (updateState (Read σ-tree) (Read (updateByFront path ((ι τ)) σ-tree)) auxξ))
        (where auxξ_new        (addReadNode τ (read con ι μ-value) path auxξ_upd_σ-tree))
))))
