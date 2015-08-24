#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "relAcqRules.rkt")
(require "naRules.rkt")
(require "scRules.rkt")

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
                  getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo_t))

(define relAcqRules (define-relAcqRules etaPsiSCLang
                      synchronizeWriteFront isReadQueueEqualTo_t))
(define naRules     (define-naRules     etaPsiSCLang
                      defaultState getWriteσ_nil ιNotInReadQueue_t))

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
(define testTerm3
         (term (((write sc "c" 0) >>= (λ x
                    (spw
                     ((write na "a" 7) >>= (λ x
                      (write sc "c" 1)))
                     ((repeat (read sc "c")) >>= (λ x
                     ((read  na "a") >>= (λ x
                      (write na "a" (+ 1 x))))
                      ))
                    )))
                    >>= (λ x (read na "a")))))
#|
(test-->> step
         (term (,testTerm3 defaultState))
         (term (stuck defaultState)))
|#
; (traces step (term (,testTerm3 defaultState)))
