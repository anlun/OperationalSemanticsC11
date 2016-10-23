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
  (define-naRules etaPsiLang etaPsiDefaultState))

(define naStep
  (union-reduction-relations etaPsiCoreStep naRules))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#

(test-->>∃ naStep testTerm2
          (term stuck))

;;;;;;;;;;;;;;;;;;
; Rel/Acq
;;;;;;;;;;;;;;;;;;

(define relAcqRules
  (define-relAcqRules etaPsiLang))
(define relAcqStep
  (union-reduction-relations etaPsiCoreStep relAcqRules))

#|
x_rel  = 1 || y_rel = 1
R1 = y_acq || R2 = x_acq

Can lead to R1 = R2 = 0.
|#

(test-->>∃ relAcqStep term_WrelRacq_WrelRacq
          (term (ret (0 0))))

#|
IRIW. Anti-TSO example. (Release+Acquire)

                     x_rel = 0
                     y_rel = 0
x_rel = 1 || y_rel = 1 || a = x_acq || c = y_acq
          ||           || b = y_acq || d = x_acq

The `ret ((1 0) (0 1))` shows that our model is more relaxed
than x86-TSO [Sewell-al:CACM10].
|#

;; (test-->>∃ relAcqStep testTerm67
;;           (term (ret ((1 0) (0 1)))))

#| CoRR_rel+acq (Coherence of Read-Read)
                     x_rel = 0
x_rel = 1 || x_rel = 2 || a = x_acq || c = x_acq
          ||           || b = x_acq || d = x_acq

The execution a = d = 1 and b = c = 2 should be invalid.
|#
;; (test-->>∃ relAcqStep test_CoRR_rel+acq
;;           (term (ret ((0 0) (0 0))))
;;           (term (ret ((0 0) (0 1))))
;;           (term (ret ((0 0) (1 1))))
;;           (term (ret ((0 1) (0 0))))
;;           (term (ret ((0 1) (0 1))))
;;           (term (ret ((0 1) (0 1)))))


;;;;;;;;;;;;;;;;;;
; Rlx
;;;;;;;;;;;;;;;;;;

(define rlxReadRules  (define-rlxReadRules etaPsiLang))
(define rlxRules      (define-rlxRules     etaPsiLang))
(define rlxStep       (union-reduction-relations etaPsiCoreStep rlxRules))

#|
x_rlx  = 1 || y_rlx  = 1
R1 = y_rlx || R2 = x_rlx

Can lead to R1 = R2 = 0.
|#
(test-->>∃ rlxStep term_WrlxRrlx_WrlxRrlx 
          (term (ret (0 0))))

#|
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 is invalid.
As well as a = d = 2 and b = c = 1.
I don't know how to say 'this can't be reduced to that' in tests, so this test should fail.
|#

(define (not1221 b)
  (not (or (equal? (term ((ret ((1 2) (2 1))) etaPsiDefaultState))
                   b)
           (equal? (term ((ret ((2 1) (1 2))) etaPsiDefaultState))
                   b))))

;; (test-->> rlxStep testTerm6 
;;          )
;;          (term (ret ((1 2) (2 1))))
;;          (term (ret ((2 1) (1 2))))

#|
IRIW. Anti-TSO example.

                     x_rlx = 0
                     y_rlx = 0
x_rlx = 1 || y_rlx = 1 || a = x_rlx || c = y_rlx
          ||           || b = y_rlx || d = x_rlx

The `ret ((1 0) (0 1))` shows that our model is more relaxed
than x86-TSO [Sewell-al:CACM10].
|#

(test-->>∃ rlxStep testTerm65
          (term (ret ((1 0) (0 1)))))


#|
Anti-TSO example.
It shows why our model isn't TSO.

  x_rlx = 0; y_rlx = 0
x_rlx = 1; || a = y_rlx;
y_rlx = 1  || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.
|#
(test-->>∃ rlxStep testTerm7
           (term (ret (1 0))))


;;;;;;;;;;;;;;;;;;
; Postponed Reads
;;;;;;;;;;;;;;;;;;

(define postponedReadRules (define-postponedReadRules postReadLang postponedReadDefaultState))
(define rlxWriteRules      (define-rlxWriteRules      postReadLang))
(define postponedReadStep  (union-reduction-relations postponedReadCoreStep rlxWriteRules postponedReadRules))


(test-->>∃ postponedReadStep term_WrlxRrlx_WrlxRrlx
          (term (ret (0 0))))

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(test-->>∃ postponedReadStep term_RrlxWrlx_RrlxWrlx
          (term (ret (1 1))))

