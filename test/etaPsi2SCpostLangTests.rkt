#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/postReadRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/scRules.rkt")
(require "testTerms.rkt")
(require "../core/langs.rkt")

(define-term defaultState (() (Read ()) (Write ()) (SC ()) (P ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_2ψ_φ joinST_2ψ_φ isReadQueueEqualTo)
   etaPsi2SCpostLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define postponedReadRules (define-postponedReadRules etaPsi2SCpostLang))
(define rlxWriteRules      (define-rlxWriteRules      etaPsi2SCpostLang
                             getWriteσ_2ψ isReadQueueEqualTo ιNotInReadQueue))
(define relAcqWriteRules   (define-relAcqWriteRules etaPsi2SCpostLang
                             addReadNode_t
                             synchronizeWriteFront isReadQueueEqualTo
                             addWriteNode_t))
(define scRules            (define-scRules            etaPsi2SCpostLang
                             getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo))
(define step (union-reduction-relations
              coreStep
              postponedReadRules
              rlxWriteRules
              relAcqWriteRules
              scRules))
#|
y_rlx  = 1 || x_rlx  = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(test-->>∃ step
          (term (,testTerm0  defaultState))
          (term ((ret (0 0)) defaultState)))

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(test-->>∃ step
          (term (,testTerm01 defaultState))
          (term ((ret (1 1)) defaultState)))
#|
R1 = x_rlx || R2 = y_rlx
y_rel  = 1 || x_rel   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
Release modificators solve nothing here.
|#
(test-->>∃ step
          (term (,testTerm02 defaultState))
          (term ((ret (1 1)) defaultState)))

#|
R1 = x_rlx || R2 = y_rlx
y_sc   = 1 || x_sc   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
SC modificators solve nothing here.
|#
(test-->>∃ step
          (term (,testTerm03 defaultState))
          (term ((ret (1 1)) defaultState)))

#|
        c_rlx = 0
        x_rlx = c
a_rlx = 239; || b = x_acq;
x_rel = a    || res = b_rlx
          ret res
|#
(define testTerm11
  (term ((write rlx "c"   0) >>= (λ x
        ((write rlx "x" "c") >>= (λ x
        ((spw
          ((write rlx "a" 239) >>= (λ x
           (write rel "x" "a")))
          ((read  acq "x") >>= (λ b
           (read  rlx b)))) >>= (λ res
        (ret (proj2 res))))))))))

(test-->> step
          (term (,testTerm11 defaultState))
          (term ((ret 0) defaultState))
          (term ((ret 239) defaultState)))
