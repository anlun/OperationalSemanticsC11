#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/langs.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")

(define-term defaultState (() (Read ()) (Write ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_2ψ joinST_2ψ isReadQueueEqualTo_t)
   etaPsi2Lang #:domain ξ))

(define coreTest (define-coreTest coreStep defaultState))


(define rlxReadRules  (define-rlxReadRules  etaPsi2Lang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2Lang
                        getWriteσ_2ψ isReadQueueEqualTo_t ιNotInReadQueue_t))
(define relAcqRules   (define-relAcqRules   etaPsi2Lang
                        addReadNode_t
                        synchronizeWriteFront isReadQueueEqualTo_t addWriteNode_t))
(define naRules       (define-naRules       etaPsi2Lang
                        addReadNode_t
                        defaultState getWriteσ_2ψ ιNotInReadQueue_t
                        addWriteNode_t))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules))

#|
       c_rlx = 0;
a_na  = 7; || repeat (c_rlx) end;
c_rlx = 1  || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It uses rlx writes and reads instead of rel/acq, and it leads to `stuck`.
|#
(test-->>∃ step
         (term (,testTerm3-0 defaultState))
         (term (stuck defaultState)))

#|
       c_rlx = 0;
a_rlx = 7; || if (c_acq)
c_rel = 1  ||   a_rlx = a_rlx + 1
       ret a_rlx
|#
(test-->> step
         (term (,testTerm3-1 defaultState))
         (term ((ret 7) defaultState))
         (term ((ret 8) defaultState)))

#|
An example from Vafeiadis-Narayan:OOPSLA13. It shouldn't get `stuck`.

                    lock = 1
a_na     = 2 || if ((cas_acq_rlx lock 0 1) || if ((cas_acq_rlx lock 0 1)
lock_rel = 0 ||     == 0)                  ||     == 0)
             || then                       || then
             ||    a_na = 3                ||    a_na = 2
             || else (ret -1)              || else (ret -1)
|#
(test-->> step
          (term (,testTerm9 defaultState))
          (term ((ret (0 (-1 -1))) defaultState))
          (term ((ret (0 (-1  2))) defaultState))
          (term ((ret (0 ( 3 -1))) defaultState)))