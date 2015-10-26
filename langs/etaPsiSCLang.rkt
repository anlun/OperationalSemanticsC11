#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")
(require "../tests/testTerms.rkt")

(define-extended-language etaPsiSCLang coreLang
  ; State:
  ; AST      -- current state of program tree;
  ; η        -- current heap history;
  ; (Read ψ) -- current threads read fronts;  
  ; (SC σ)   -- front after last SC operation;
  ; θ        -- extension point for auxilirary state.
  [auxξ (θ ... η θ ... (Read ψ) θ ... (SC σ) θ ...)])

(define-term defaultState (() (Read ()) (SC ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_readψ joinST_readψ isReadQueueEqualTo_t)
   etaPsiSCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define scRules (define-scRules etaPsiSCLang
                  getReadσ updateReadσ synchronizeWriteFront_id isReadQueueEqualTo_t))

(define relAcqRules (define-relAcqRules etaPsiSCLang
                      addReadNode_t
                      synchronizeWriteFront_id isReadQueueEqualTo_t addWriteNode_t))
(define naRules     (define-naRules     etaPsiSCLang
                      addReadNode_t
                      defaultState getWriteσ_nil ιNotInReadQueue_t
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
#|
(test-->> step
         (term (,testTerm3-2 defaultState))
         (term (stuck defaultState)))
|#
; (traces step (term (,testTerm3-2 defaultState)))

#|
  x_rel = 0; y_rel = 0
x_rel = 5  || y_rel = 5
a_sc  = 0  || b_sc  = 0
r1 = y_acq || r2 = x_acq
       ret r1 r2

In Batty-al:POPL11 it's possible to get r1 = 0 /\ r2 = 0.
|#

(test-->>∃ step
           (term (,testTerm10 defaultState))
           (term ((ret (0 0)) defaultState)))
