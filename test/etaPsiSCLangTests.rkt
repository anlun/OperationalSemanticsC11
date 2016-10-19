#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")
(require "testTerms.rkt")
(require "../core/langs.rkt")

(define-term defaultState (() (Read ()) (NA ()) (SC ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState joinST-readψ)
   etaPsiSCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define scRules (define-scRules etaPsiSCLang
                  getReadσ updateReadσ synchronizeWriteFront_id
                  are∀PostReadsRlx))

(define relAcqRules (define-relAcqRules etaPsiSCLang
                      addReadNode_t
                      synchronizeWriteFront_id
                      are∀PostReadsRlx
                      addWriteNode_t))
(define naRules     (define-naRules     etaPsiSCLang
                      addReadNode_t
                      defaultState getWriteσ_nil
                      addWriteNode_t))

(define step (union-reduction-relations coreStep relAcqRules naRules scRules))

#|
       c_sc = 0;
a_na  = 7; || repeat (c_sc) end;
c_sc = 1   || a_na = a_na + 1
       ret a_na

Version with SC modifiers instead of Rel/Acq.
Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".

It shouldn't get `stuck`.
|#
(test-->> step
         (term (,testMP+sc defaultState))
         (term ((ret 8) defaultState)))

#|
  x_rel = 0; y_rel = 0
x_rel = 5  || y_rel = 5
a_sc  = 0  || b_sc  = 0

       ret r1 r2

In Batty-al:POPL11 it's possible to get r1 = 0 /\ r2 = 0.
|#
(test-->>∃ step
           (term (,testTerm10 defaultState))
           (term ((ret (0 0)) defaultState)))

#|
  x_rel = 0; y_rel = 0
x_sc  = 1  || y_sc  = 1
r1 = y_sc  || r2 = x_sc
       ret r1 r2
|#
(test-->>∃ step
           (term (,term_WscRsc_WscRsc defaultState))
           (term ((ret (1 1)) defaultState)))

(define (runTestTerm12 termToTest)
  (test-->> step
           (term (,termToTest defaultState))
           (term ((ret (0 0)) defaultState))
           (term ((ret (0 1)) defaultState))
           (term ((ret (1 0)) defaultState))
           (term ((ret (1 1)) defaultState))))
(runTestTerm12 term_WrelRsc_WscRsc)
(runTestTerm12 term_WscRacq_WscRsc)
(runTestTerm12 term_WscRsc_WrelRsc)
(runTestTerm12 term_WscRsc_WscRacq)

#|
   x_rel = 0; y_rel = 1
x_mod0 = 1  || y_mod2 = 2
r1 = y_mod1 || r2 = x_mod3
       ret (r1 r2)
|#
(define (test_W1R_W2R curTerm)
  (test-->>∃ step
           (term (,curTerm defaultState))
           (term ((ret (1 0)) defaultState))))

(test_W1R_W2R term_W1relRacq_W2relRacq)

#|
   x_rel = 0; y_rel = 1
x_sc = 1  || y_rel = 2
r1 = y_sc || r2 = x_acq
       ret (r1 r2)
|#
(test_W1R_W2R term_W1scRsc_W2relRacq)

#|
   x_rel = 0; y_rel = 1
x_sc = 1  || y_sc = 2
r1 = y_sc || r2 = x_acq
       ret (r1 r2)
|#
(test_W1R_W2R term_W1scRsc_W2scRacq)

#|
x_rel = 1     || y_rel = 1
fence_sc      || fence_sc
r1 = y_acq    || r2 = x_acq
       ret (r1, r2)

r1 = 0, r2 = 0 - is not allowed
|#
(test-->> step
         (term (,testSB+rel+acq+fences+sc defaultState))
         (term ((ret (0 1)) defaultState))
         (term ((ret (1 0)) defaultState))
         (term ((ret (1 1)) defaultState)))

