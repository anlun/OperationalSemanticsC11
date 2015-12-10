#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")
(require "../core/pp.rkt")
(require "../core/langs.rkt")

(define relAcqRules (define-relAcqRules etaPsiLang
                      addReadNode_t
                      synchronizeWriteFront_id isReadQueueEqualTo_t
                      are∀PostReadsRlx ιNotInReadQueue
                      addWriteNode_t))
(define naRules     (define-naRules     etaPsiLang
                      addReadNode_t
                      etaPsiDefaultState getWriteσ_nil ιNotInReadQueue
                      addWriteNode_t))
(define step        (union-reduction-relations etaPsiCoreStep relAcqRules naRules))

#|
       c_rel = 0;
a_na  = 7; || repeat (c_acq) end;
c_rel = 1  || a_na = a_na + 1
       ret a_na

Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(test-->> step
         (term (,testTerm3 etaPsiDefaultState))
         (term ((ret 8) etaPsiDefaultState)))

;(traces step (term (,testTerm3 etaPsiDefaultState)))

#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rel = 0;
               y_rel = 0;
x_rel = 1;         || y_rel = 1;
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(test-->>∃ step
         (term (,testTerm4 etaPsiDefaultState))
         (term (stuck etaPsiDefaultState)))

;(traces step (term (,testTerm4 etaPsiDefaultState)) #:pp pretty-printer)
;(stepper step (term (,testTerm4 etaPsiDefaultState)) pretty-printer)

#|
Ernie Cohen's lock should work in weak memory settings.
Described in Turon-al:OOPSLA14.

                   x_rel = 0;
                   y_rel = 0;
x_rel = choice(1, 2);  || y_rel = choice(1, 2); 
repeat y_acq end;      || repeat x_acq end;
if x_acq == y_acq then || if x_acq != y_acq then
  a_na = 239           ||   a_na = 239

|#
(test-->> step
         (term (,testTerm5 etaPsiDefaultState))
         (term ((ret (0 239)) etaPsiDefaultState))
         (term ((ret (239 0)) etaPsiDefaultState)))

#|
      x_rel = 0
x_rel = 1 || r = x_acq
x_na  = 2 ||

Should lead to `stuck` because of VafeiadisNarayan:OOPSLA (ConsistentRFna) ---
`x_na = 2` and `r = x_acq` aren't happens-before ordered.
|#
(test-->>∃ step
           (term (,term_WrelWna_Racq etaPsiDefaultState))
           (term (stuck etaPsiDefaultState)))
