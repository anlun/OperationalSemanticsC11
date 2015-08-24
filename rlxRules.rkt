#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "etaPsiLang.rkt")
(require "testTerms.rkt")
(provide define-rlxRules define-rlxReadRules define-rlxWriteRules)

(define-syntax-rule (define-rlxReadRules lang)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (--> ((in-hole E (read  rlx ι)) auxξ)
        ((in-hole E (ret μ-value)) auxξ_new)
        "read-rlx"
        (where η      (getη auxξ))
        (where ψ      (getReadψ auxξ))
        (where path   (pathE E))

        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where auxξ_new (updateState (Read ψ) (Read (updateByFront path ((ι τ)) ψ)) auxξ))

        (where σ_read   (getByPath path ψ))
        (side-condition (term (correctτ τ ι σ_read))))
   )))

(define-syntax-rule (define-rlxWriteRules lang getWriteσ isReadQueueEqualTo ιNotInReadQueue)
  (begin

  (reduction-relation
   lang #:domain ξ
   
   (--> ((in-hole E (write rlx ι μ-value)) auxξ)
        ((in-hole E (ret 0))               auxξ_new)
        "write-rlx"
        (where η       (getη auxξ))
        (where ψ_read  (getReadψ  auxξ))
        (where path    (pathE E))

        (where τ              (getNextTimestamp ι η))
        (where ψ_read_new     (updateByFront path ((ι τ)) ψ_read))
        (where auxξ_upd_front (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ_write    (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new      (updateCell ι μ-value σ_write η))
        (where auxξ_new   (updateState η η_new auxξ_upd_front))

        (side-condition (term (ιNotInReadQueue_t ι path auxξ))))

   (--> ((in-hole E (cas SM rlx ι μ-value_expected μ-value)) auxξ)
        ((in-hole E (ret 0                                )) auxξ_new)
        "cas-fail-rlx"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))
        (where τ        (getLastTimestamp ι η))
        (where auxξ_new (updateState (Read ψ_read) (Read (updateByFront path ((ι τ)) ψ_read)) auxξ))

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM rlx)))
        (side-condition (term (isReadQueueEqualTo () path auxξ))))

   (--> ((in-hole E (cas rlx FM ι μ-value_expected μ-value_new)) auxξ)
        ((in-hole E (ret 1                                    )) auxξ_new)
        "cas-succ-rlx"
        (where η        (getη     auxξ))
        (where ψ_read   (getReadψ auxξ))
        (where path     (pathE E))

        (where τ             (getNextTimestamp ι η))
        (where ψ_read_new    (updateByFront path ((ι τ)) ψ_read))
        (where auxξ_upd_read (updateState (Read ψ_read) (Read ψ_read_new) auxξ))

        (where σ_write    (updateFront ι τ (getWriteσ path auxξ)))
        (where η_new      (updateCell  ι μ-value σ_write η))
        (where auxξ_new   (updateState η η_new auxξ_upd_read))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rlx FM)))
        (side-condition (term (ιNotInReadQueue ι path auxξ))))
)))

(define-syntax-rule (define-rlxRules lang getWriteσ isReadQueueEqualTo_t ιNotInReadQueue)
  (begin

  (union-reduction-relations
   (define-rlxReadRules lang)
   (define-rlxWriteRules lang getWriteσ isReadQueueEqualTo ιNotInReadQueue))
))

(define rlxReadRules  (define-rlxReadRules  etaPsiLang))
(define rlxRules      (define-rlxRules etaPsiLang
                        getWriteσ_nil isReadQueueEqualTo_t ιNotInReadQueue_t))
(define step          (union-reduction-relations coreStep rlxRules))

;;;;;;;;;;;;;;;;;
; Tests
;;;;;;;;;;;;;;;;;

#|
y_rlx  = 1 || x_rlx  = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(test-->>∃ step
          (term (,testTerm0  defaultState))
          (term ((ret (0 0)) defaultState)))

#|
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 is invalid.
I don't know how to say 'this can't be reduced to that' in tests, so this test should fail.
|#
#|
(test-->>∃ step
          (term (,testTerm0  defaultState))
          (term ((ret ((1 2) (2 1))) defaultState)))
|#

#|
IRIW. Anti-TSO example.

                     x_rlx = 0
                     y_rlx = 0
x_rlx = 1 || y_rlx = 1 || a = x_rlx || c = y_rlx
          ||           || b = y_rlx || d = x_rlx

The test takes too many time to execute. Results are:

  actual: '((ret ((0 0) (0 0))) (() (Read ())))
  actual: '((ret ((0 0) (0 1))) (() (Read ())))
  actual: '((ret ((0 0) (1 0))) (() (Read ())))
  actual: '((ret ((0 0) (1 1))) (() (Read ())))
  actual: '((ret ((0 1) (0 0))) (() (Read ())))
  actual: '((ret ((0 1) (0 1))) (() (Read ())))
  actual: '((ret ((0 1) (1 0))) (() (Read ())))
  actual: '((ret ((0 1) (1 1))) (() (Read ())))
  actual: '((ret ((1 0) (0 0))) (() (Read ())))
  actual: '((ret ((1 0) (0 1))) (() (Read ())))
  actual: '((ret ((1 0) (1 0))) (() (Read ())))
  actual: '((ret ((1 0) (1 1))) (() (Read ())))
  actual: '((ret ((1 1) (0 0))) (() (Read ())))
  actual: '((ret ((1 1) (0 1))) (() (Read ())))
  actual: '((ret ((1 1) (1 0))) (() (Read ())))
  actual: '((ret ((1 1) (1 1))) (() (Read ())))

The `ret ((1 0) (0 1))` shows that our model is more relaxed than x86-TSO [Sewell-al:CACM10].
|#
#|
(test-->> step
          (term (,testTerm65 defaultState))
          (term ((ret ((1 0) (1 0))) defaultState)))
|#

#|
Anti-TSO example.
It shows why our model isn't TSO.

      x = 0; y = 0
x_rlx = 1; || a = y_rlx;
y_rlx = 1  || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.
|#
(test-->>∃ step
           (term (,testTerm7 defaultState))
           (term ((ret (1 0)) defaultState)))