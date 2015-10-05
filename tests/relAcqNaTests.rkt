#lang racket
(require redex)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../langs/etaPsiLang.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")
(require "../core/pp.rkt")

(define relAcqRules (define-relAcqRules etaPsiLang
                      addReadNode_t addSWedges_t
                      synchronizeWriteFront_id isReadQueueEqualTo_t
                      addWriteNode_t))
(define naRules     (define-naRules     etaPsiLang
                      addReadNode_t
                      defaultState getWriteσ_nil ιNotInReadQueue_t
                      addWriteNode_t))
(define step        (union-reduction-relations coreStep relAcqRules naRules))

#|
       c_rel = 0;
a_na  = 7; || repeat (c_acq) end;
c_rel = 1  || a_na = a_na + 1
       ret a_na

Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
#|
(test-->> step
         (term (,testTerm3 defaultState))
         (term (stuck defaultState)))
|#
;(traces step (term (,testTerm3 defaultState)))

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
         (term (,testTerm4 defaultState))
         (term (stuck defaultState)))

(traces step (term (,testTerm4 defaultState)) #:pp pretty-printer)
;(stepper step (term (,testTerm4 defaultState)) pretty-printer)

#|
Ernie Cohen's lock should work in weak memory settings.
Described in Turon-al:OOPSLA14.

                   x_rel = 0;
                   y_rel = 0;
x_rel = choice(1, 2);  || y_rel = choice(1, 2); 
repeat y_acq end;      || repeat x_acq end;
if x_acq == y_acq then || if x_acq != y_acq then
  a_na = 239           ||   a_na = 239


Unfortunately, DrRacket can't find fixpoint in normal time in this case.
|#
#|
(test-->> step
         (term (,testTerm5 defaultState))
         (term ((ret 239) deafultState)))
|#