#lang racket
(require redex/reduction-semantics)
;(require redex)
;(require "../core/pp.rkt")
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")

#|
                     x_rlx = 0; a_rlx = 0; b_rlx = 0
a_rlx = 1 || b_rlx = 1            || if (x_rlx = 2) { || rX = x_acq
x_rel = 1 || cas_rel,rlx(x, 1, 2) ||   x_rlx = 3      || rA = a_rlx
                                  || } else { ret 0 } || rB = b_rlx
                          ret (rX (rA rB))

Possible outcomes according to Batty-al:POPL11:
rX |rA  |rB
-------------
0  |0,1 |0,1
1  |1   |0,1
2  |1   |1
3  |0,1 |1
|#

(define term_WW_WRMW_W_RRR
  (term
   ((write rlx "x" 0) >>= (λ z
   ((write rlx "a" 0) >>= (λ z
   ((write rlx "b" 0) >>= (λ z
   ((spw
     (spw
      ((write rlx "a" 1) >>= (λ z
       (write rel "x" 1)))
      ((write rlx "b" 1) >>= (λ z
       (cas rel rlx "x" 1 2))))
     ((spw
      ((read rlx "x") >>= (λ xV
       (if (== xV 2)
           (write rlx "x" 3)
           (ret 0))))
      ((read acq "x") >>= (λ rX
      ((read rlx "a") >>= (λ rA
      ((read rlx "b") >>= (λ rB
       (ret (rX (rA rB))))))))))
      >>= (λ x (ret (proj2 x)))))
    >>= (λ x (ret (proj2 x))))))))))))

(define term_Big
  (term
   ((write rlx "x" 0) >>= (λ z
    (spw
     (spw
      (write rlx "x" 1)
      (write rlx "x" 2))
     (spw
      (read rlx "x")
      (read rlx "x")))))))

;(test-->> step
;          (term (,term_Big defaultState))
;          (term ((ret 0) defaultState)))

;(traces step (term (,term_Big defaultState)) #:pp pretty-printer)

#|
(test-->> step
          (term (,term_WW_WRMW_W_RRR defaultState))
          (term (ret (0 (0 0))))
          (term (ret (0 (0 1))))
          (term (ret (0 (1 0))))
          (term (ret (0 (1 1))))

          (term (ret (1 (1 0))))
          (term (ret (1 (1 1))))
          
          (term (ret (2 (1 1))))

          (term (ret (3 (0 1))))
          (term (ret (3 (1 1)))))
|#

;(traces step (term (,term_WW_WRMW_W_RRR defaultState)))
