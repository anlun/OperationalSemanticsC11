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

(define-term defaultState (() (Read ()) (NA ()) (Write ()) (SC ()) (P ()) (R ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST_2ψ_φ joinST_2ψ_φ isReadQueueEqualTo)
   etaPsi2SCpostLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define postponedReadRules (define-postponedReadRules etaPsi2SCpostLang))
(define rlxWriteRules      (define-rlxWriteRules      etaPsi2SCpostLang
                             getWriteσ_2ψ isReadQueueEqualTo ιNotInReadQueue))
(define relAcqWriteRules   (define-relAcqWriteRules   etaPsi2SCpostLang
                             addReadNode_t
                             synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue 
                             addWriteNode_t))
(define scRules            (define-scRules            etaPsi2SCpostLang
                             getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue))
(define step (union-reduction-relations
              coreStep
              postponedReadRules
              rlxWriteRules
              relAcqWriteRules
              scRules))

#|
y_{rel,rlx}  = 1 || x_{rel,rlx}  = 1
R1 = x_{acq,rlx} || R2 = y_{acq,rlx}

Can lead to R1 = R2 = 0.
|#
(define (test_WR_WR_00 curTerm)
  (test-->>∃ step
          (term (,term_WrlxRrlx_WrlxRrlx  defaultState))
          (term ((ret (0 0)) defaultState))))
(test_WR_WR_00 term_WrlxRrlx_WrlxRrlx)
(test_WR_WR_00 term_WrelRacq_WrelRacq)

#|
R1 = x_rlx            || R2 = y_rlx
y_{sc, rel, rlx}  = 1 || x_{sc, rel, rlx}  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(define (test_RW_RW_11 curTerm)
  (test-->>∃ step
          (term (,curTerm defaultState))
          (term ((ret (1 1)) defaultState))))
(test_RW_RW_11 term_RrlxWrlx_RrlxWrlx)
(test_RW_RW_11 term_RrlxWrel_RrlxWrel)
(test_RW_RW_11 term_RrlxWsc_RrlxWsc)

#|
R1 = x_{acq,rlx}  || R2 = y_{acq,rlx} 
y_rel  = 1        || x_rel  = 1

Without rlx/rlx combination it's impossible to get R1 = R2 = 1.
|#
(define (test_RW_RW_n11 curTerm)
  (test-->> step
          (term (,curTerm defaultState))
          (term ((ret (0 0)) defaultState))
          (term ((ret (1 0)) defaultState))
          (term ((ret (0 1)) defaultState))))
(test_RW_RW_n11 term_RacqWrel_RrlxWrel)
(test_RW_RW_n11 term_RrlxWrel_RacqWrel)
(test_RW_RW_n11 term_RacqWrel_RacqWrel)

#|
          x_rlx = 0; y_rlx = 0
     y_rlx = 1     || if (x_acq == 2) {
     x_rel = 1     ||    r1 = y_rlx 
x_rlx = 2 || ret 0 || } else {
                   ||    r1 = 1 }             

According to Batty-al:POPL11 it's possible to get r1 = 0, because
there is no release sequence between x_rel = 1 and x_rlx = 2.
|#
(test-->>∃ step
           (term (,term_Wrel_Wrlx_Racq defaultState))
           (term ((ret 0) defaultState)))
 
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
