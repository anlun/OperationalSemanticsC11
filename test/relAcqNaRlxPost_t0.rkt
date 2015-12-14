#lang at-exp racket
(require redex/reduction-semantics)
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

#|
y_{rel,rlx}  = 1 || x_{rel,rlx}  = 1
R1 = x_{acq,rlx} || R2 = y_{acq,rlx}

Can lead to R1 = R2 = 0.
|#
(define (test_WR_WR_00 curTerm)
  (test-->>∃ step
          (term (,curTerm  defaultState))
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
  @prog{c_rlx := 0;
        x_rlx := c;
        r0 := spw
              {{{ a_rlx := 239;
                  x_rel := a
              ||| r1 := x_acq;
                  r1_rlx }}};
        ret r0_2 })

(test-->> step
          (term (,testTerm11 defaultState))
          (term ((ret 0) defaultState))
          (term ((ret 239) defaultState)))

#|
   x_rlx = 0; y_rlx = 0;
R1 = x_acq || R2 = y_rlx
y_rlx  = 1 || x_rel  = 1
           || x_rlx  = 2

With postponed reads it shouldn't lead to R1 = 2; R1 = 1.
|#
(test-->> step
          (term (,term_RacqWrlx_RrlxWrelWrlx defaultState))
          (term ((ret (0 0)) defaultState))
          (term ((ret (1 0)) defaultState))
          (term ((ret (2 0)) defaultState))
          (term ((ret (0 1)) defaultState)))

