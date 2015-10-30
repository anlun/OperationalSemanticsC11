#lang racket
(require redex/reduction-semantics)
(require "../core/coreUtils.rkt")
(require "../core/langs.rkt")
(require "testTerms.rkt")
(require "../rules/naRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/scRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/postReadRules.rkt")

;;;;;;;;;;;;;;;;;;
; NA
;;;;;;;;;;;;;;;;;;

(define naRules
  (define-naRules etaPsiLang addReadNode_t etaPsiDefaultState getWriteσ_nil ιNotInReadQueue_t addWriteNode_t))

(define naStep
  (union-reduction-relations etaPsiCoreStep naRules))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(test-->>∃ naStep
          (term (,testTerm2 etaPsiDefaultState))
          (term (stuck etaPsiDefaultState)))

;;;;;;;;;;;;;;;;;;
; Rel/Acq
;;;;;;;;;;;;;;;;;;

(define relAcqRules
  (define-relAcqRules etaPsiLang addReadNode_t
    synchronizeWriteFront_id isReadQueueEqualTo_t addWriteNode_t))
(define relAcqStep
  (union-reduction-relations etaPsiCoreStep relAcqRules))

#|
y_rel  = 1 || x_rel = 1
R1 = x_acq || R2 = y_acq

Can lead to R1 = R2 = 0.
|#
(test-->>∃ relAcqStep
          (term (,testTerm1 etaPsiDefaultState))
          (term ((ret (0 0)) etaPsiDefaultState)))

;;;;;;;;;;;;;;;;;;
; Rlx
;;;;;;;;;;;;;;;;;;

(define rlxReadRules  (define-rlxReadRules etaPsiLang))
(define rlxRules      (define-rlxRules     etaPsiLang
                        getWriteσ_nil isReadQueueEqualTo_t ιNotInReadQueue_t))
(define rlxStep       (union-reduction-relations etaPsiCoreStep rlxRules))

#|
y_rlx  = 1 || x_rlx  = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(test-->>∃ rlxStep
          (term (,testTerm0  etaPsiDefaultState))
          (term ((ret (0 0)) etaPsiDefaultState)))

#|
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 is invalid.
I don't know how to say 'this can't be reduced to that' in tests, so this test should fail.
|#
#|
(test-->>∃ rlxStep
          (term (,testTerm0  etaPsiDefaultState))
          (term ((ret ((1 2) (2 1))) etaPsiDefaultState)))
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
(test-->> rlxStep
          (term (,testTerm65 etaPsiDefaultState))
          (term ((ret ((1 0) (1 0))) etaPsiDefaultState)))
|#

#|
Anti-TSO example.
It shows why our model isn't TSO.

      x = 0; y = 0
x_rlx = 1; || a = y_rlx;
y_rlx = 1  || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.
|#
(test-->>∃ rlxStep
           (term (,testTerm7 etaPsiDefaultState))
           (term ((ret (1 0)) etaPsiDefaultState)))


;;;;;;;;;;;;;;;;;;
; Postponed Reads
;;;;;;;;;;;;;;;;;;

(define postponedReadRules (define-postponedReadRules postReadLang))
(define rlxWriteRules      (define-rlxWriteRules      postReadLang
                             getWriteσ_nil isReadQueueEqualTo ιNotInReadQueue))
(define postponedReadStep  (union-reduction-relations postponedReadCoreStep rlxWriteRules postponedReadRules))

(test-->>∃ postponedReadStep
          (term (,testTerm0  postponedReadDefaultState))
          (term ((ret (0 0)) postponedReadDefaultState)))

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#

(test-->>∃ postponedReadStep
          (term (,term_RrlxWrlx_RrlxWrlx postponedReadDefaultState))
          (term ((ret (1 1)) postponedReadDefaultState)))
