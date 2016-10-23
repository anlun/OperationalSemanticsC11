#lang racket
(require redex/reduction-semantics)
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")

#|
            x_rlx = 0; y_rlx = 0
R1 = y_mod0 || ret 0 || R2 = x_mod2 || ret 0
     x_mod1 = 1      ||      y_mod3 = 1
                ret (R1 R2)

If there is no Rel-Acq pair, then R1 = R2 = 1 should be possible.
|#
(define (test_R-W_R-W_11 curTerm)
  (test-->>∃ step curTerm
          (term (ret (1 1)))))

;; These tests require to uncomment "join-postponed-operations-interleaving"
;; rule in "rules/postReadRules.rkt".
;; It commented out as leading to very poor performance.
(define (failingTests)
  (test_R-W_R-W_11 term_Rrlx-Wrlx_Rrlx-Wrlx)
  (test_R-W_R-W_11 term_Rrlx-Wrel_Rrlx-Wrel))

;; This test requires "join-postponed-operations-interleaving" as well.
;; Also it doesn't deliver desirable behavior because of acquire reads.
;; However, the behaviour isn't observable on x86, ARM, Power with
;; existing sound compilation schemes.
(define (failingTest)
  (test_R-W_R-W_11 term_Racq-Wrlx_Racq-Wrlx))

(define (test_R-W_R-W_n11 curTerm)
  (test-->> step curTerm
          (term (ret (0 0)))
          (term (ret (1 0)))
          (term (ret (0 1)))))
(test_R-W_R-W_n11 term_Rrlx-Wrel_Racq-Wrel)

#|

             x_rlx = 0; y_rlx = 0
y_rlx = 1 || cas_rlx,rlx(x, 1, 2) || r1 = x_acq
x_rel = 1 ||                      || r2 = y_rlx

It's impossible to get r1 = 2; r2 = 0, due to synchronization through
RMW (cas) operation.
|#
(test-->> step term_WrlxWrel_RMWrlxrlx_RacqRrlx
          (term (ret (0 0)))
          (term (ret (0 1)))
          (term (ret (1 1)))
          (term (ret (2 1))))

#|
   x_rel = 0; y_rel = 1
x_mod0 = 1  || y_mod2 = 2
r1 = y_mod1 || r2 = x_mod3
       ret (r1 r2)
|#
(define (test_W1R_W2R curTerm)
  (test-->>∃ step curTerm
           (term (ret (1 0)))))

(test_W1R_W2R term_W1rlxRrlx_W2rlxRrlx)
(test_W1R_W2R term_W1relRrlx_W2relRrlx)
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

