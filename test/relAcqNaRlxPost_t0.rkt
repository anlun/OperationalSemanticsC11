#lang at-exp racket
(require redex/reduction-semantics)
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

#|
x_{rel,rlx}  = 1 || y_{rel,rlx}  = 1
R1 = y_{acq,rlx} || R2 = x_{acq,rlx}

Can lead to R1 = R2 = 0.
|#
(define (test_SB_00 curTerm)
  (test-->>∃ step
          (term (,curTerm  defaultState))
          (term ((ret (0 0)) defaultState))))
(test_SB_00 term_WrlxRrlx_WrlxRrlx)
(test_SB_00 term_WrelRacq_WrelRacq)

#|
R1 = x_{rlx, con}     || R2 = y_{rlx, con}
y_{sc, rel, rlx}  = 1 || x_{sc, rel, rlx}  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(define (test_LB_11 curTerm)
  (test-->>∃ step
          (term (,curTerm defaultState))
          (term ((ret (1 1)) defaultState))))
(test_LB_11 term_RrlxWrlx_RrlxWrlx)
(test_LB_11 term_RrlxWrel_RrlxWrel)
(test_LB_11 term_RrlxWsc_RrlxWsc)

(test_LB_11 term_RconWrlx_RconWrlx)
(test_LB_11 term_RconWrel_RconWrel)
(test_LB_11 term_RconWsc_RconWsc)

#|
R1 = x_{acq,rlx}  || R2 = y_{acq,rlx} 
y_rel  = 1        || x_rel  = 1

Without rlx/rlx combination it's impossible to get R1 = R2 = 1.
|#
(define (test_LB_n11 curTerm)
  (test-->> step
          (term (,curTerm defaultState))
          (term ((ret (0 0)) defaultState))
          (term ((ret (1 0)) defaultState))
          (term ((ret (0 1)) defaultState))))
(test_LB_n11 term_RacqWrel_RrlxWrel)
(test_LB_n11 term_RrlxWrel_RacqWrel)
(test_LB_n11 term_RacqWrel_RacqWrel)

#|
R1  = x_{rlx, con}    || R2 = y_{rlx, con}
R1' = R1 + 1          || R2' = R2 + 1
y_{sc, rel, rlx}  = 1 || x_{sc, rel, rlx}  = 1

With postponed lets and reads it should be able to lead to R1' = R2' = 2.
|#
(define (test_LB_let_22 curTerm)
  (test-->>∃ step
          (term (,curTerm defaultState))
          (term ((ret (2 2)) defaultState))))
(test_LB_let_22 term_RrlxWrlx_RrlxWrlx_let)
(test_LB_let_22 term_RrlxWrel_RrlxWrel_let)
(test_LB_let_22 term_RrlxWsc_RrlxWsc_let)

(test_LB_let_22 term_RconWrlx_RconWrlx_let)
(test_LB_let_22 term_RconWrel_RconWrel_let)
(test_LB_let_22 term_RconWsc_RconWsc_let)

#|
     x_rlx = 0; y_rlx = 0
R1  = x_mod0; || R2  = y_mod2;
z1_rlx  = R1; || z2_rlx  = R2;
y_mod1  =  1; || x_mod3  =  1;
  r1 = z1_mod0; r2 = z2_mod0

With postponed writes and reads it should be able to lead to r1 = r2 = 1.
|#

(define (test_LB_use curTerm)
  (test-->>∃ step
          (term (,curTerm defaultState))
          (term ((ret (1 1)) defaultState))))

(test_LB_use term_RrlxWrlx_RrlxWrlx_use)
(test_LB_use term_RconWrlx_RconWrlx_use)

;; Problem
;; (test_LB_use term_RrlxWrel_RrlxWrel_use)

#|
  x_mod0 = 0; y_mod0 = 0
x_mod1 = 1; || y_mod3 = 1; 
y_mod2 = 2; || x_mod4 = 2;  
 r1 = x_mod5; r2 = z2_mod5
      ret (r1 r2)

It should be possible to get r1 = r2 = 1, if there is no thread with
both release accesses. 
|#
(define (test_2+2W curTerm)
  (test-->>∃ step
          (term (,curTerm defaultState))
          (term ((ret (1 1)) defaultState))))

(test_2+2W term_2+2W_rlx)

;; Problem
;; (test_2+2W term_2+2W_rel_acq)
;; (test_2+2W term_2+2W_rel1_rlx)
;; (test_2+2W term_2+2W_rel2_rlx)
;; (test_2+2W term_2+2W_rel3_rlx)

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

With postponed reads it shouldn't lead to R1 = {1, 2} \/ R2 = 1.
|#
(test-->> step
          (term (,term_RacqWrlx_RrlxWrelWrlx defaultState))
          (term ((ret (0 0)) defaultState))
          (term ((ret (1 0)) defaultState))
          (term ((ret (2 0)) defaultState))
          (term ((ret (0 1)) defaultState)))

#|
     data_na  = 0
     dataP_na = 0
     p_rel    = 0
data_na  = 5      || r1 = p_con
dataP_na = &data  ||
p_rel    = &dataP || if (r1 != 0) {
                  ||    r3 = r1_na
                  ||    r2 = r3_na
                  || else
                  ||    r2 = 1

Possible outcomes for r2 are 1 and 5.
|#
(test-->> step
          (term (,term_MP_pointer_consume defaultState))

          (term ((ret 1) defaultState))
          (term ((ret 5) defaultState)))

#|
     data_na  = 0
     p_rel    = 0
data_na  = 5     || r1 = p_con
p_rel    = &data || if (r1 != 0) {
                 ||    r2 = r1_na
                 || else
                 ||    r2 = 1

Possible outcomes for r2 are 1 and 5.
|#

#|
WRC_rlx

      x_rlx = 0; y_rlx = 0
x_rlx = 1 || r1 = x_rlx || r2 = y_rlx
          || y_rlx = r1 || r3 = x_rlx

Possible outcome: r2 = 1 /\ r3 = 0.
|#
(test-->> step
          (term (,term_WRC_rlx defaultState))

          (term ((ret (0 0)) defaultState))
          (term ((ret (0 1)) defaultState))
          (term ((ret (1 1)) defaultState))

          (term ((ret (1 0)) defaultState)))

#|
WRC_rel+acq

      x_rel = 0; y_rel = 0
x_rel = 1 || r1 = x_acq || r2 = y_acq
          || y_rel = r1 || r3 = x_acq

Impossible outcome: r2 = 1 /\ r3 = 0.
|#
(test-->> step
          (term (,term_WRC_rel+acq defaultState))

          (term ((ret (0 0)) defaultState))
          (term ((ret (0 1)) defaultState))
          (term ((ret (1 1)) defaultState)))
