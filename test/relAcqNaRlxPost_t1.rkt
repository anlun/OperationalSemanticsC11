#lang at-exp racket
(require redex/reduction-semantics)
;(require redex)
(require "../core/pp.rkt")
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

#|
             x_rlx = 0; a_rlx = 0
a_rlx = 1 || cas_rel_rlx(x, 1, 2) || rX = x_acq
x_rel = 1 ||                      || rA = a_rlx
             ret (rX rA)

Possible outcomes according to Batty-al:POPL11:
rX |rA  
--------
0  |0,1
1  |1  
2  |1  
|#
(define term_WW_WRMW_RR
  @prog{x_rlx := 0;
        a_rlx := 0;
        r0 := spw
              {{{ spw
                  {{{ a_rlx := 1;
                      x_rel := 1
                  ||| cas_rel_rlx(x, 1, 2) }}}
              ||| rX := x_acq;
                  rA := a_rlx;
                  ret [rX rA] }}};
        ret r0_2 })

(test-->> step term_WW_WRMW_RR
          '(0 0)
          '(0 1)

          '(1 1)
          
          '(2 1))

(define term_WWW_RR
  @prog{x_rlx := 0;
        a_rlx := 0;
        r0 := spw
              {{{ a_rlx := 1;
                  x_rel := 1;
                  x_rlx := 2
              ||| rX := x_acq;
                  rA := a_rlx;
                  ret [rX rA] }}};
        ret r0_2 })

(test-->> step term_WWW_RR
          '(0 0)
          '(0 1)

          '(1 1)
          
          '(2 1))

#|
             x_rlx = 0; a_rlx = 0
a_rlx = 1 || cas_rlx_rlx(x, 1, 2) || rX = x_acq
x_rel = 1 ||                      || rA = a_rlx
x_rlx = 3 ||                      ||
             ret (rX rA)

Possible outcomes according to Batty-al:POPL11:
rX |rA  
--------
0  |0,1
1  |1  
2  |1  
3  |1
|#
(define term_WWW_WRMW_RR
  @prog{x_rlx := 0;
        a_rlx := 0;
        r0 := spw
              {{{ r1 := spw
                        {{{ a_rlx := 1;
                            x_rel := 1;
                            x_rlx := 3
                        ||| cas_rlx_rlx(x, 1, 2) }}};
                  ret r1_2
              ||| rX := x_acq;
                  rA := a_rlx;
                  ret [rX rA] }}};
        ret r0 })

(test-->> step term_WWW_WRMW_RR

          '(0 (0 0))
          '(0 (0 1))
          '(0 (1 1))
          '(0 (3 1))

          '(1 (0 0))
          '(1 (0 1))
          '(1 (1 1))
          '(1 (2 1))
          '(1 (3 1))

          '(3 (0 0))
          '(3 (0 1))
          '(3 (1 1))
          '(3 (3 1)))

#|
                     x_rlx = 0; a_rlx = 0; b_rlx = 0
a_rlx = 1 || b_rlx = 1            || if (x_rlx == 2) { || rX = x_acq
x_rel = 1 || cas_rel_rlx(x, 1, 2) ||   x_rlx = 3       || rA = a_rlx
                                  || } else { ret 0 }  || rB = b_rlx
                          ret (rX (rA rB))

Possible outcomes according to Batty-al:POPL11:
rX |rA  |rB
-------------
0  |0,1 |0,1
1  |1   |0,1
2  |1   |1
3  |0,1 |0,1
|#

(define term_WW_WRMW_W_RRR
  @prog{x_rlx := 0;
        a_rlx := 0;
        b_rlx := 0;
        r0 := spw
              {{{ spw
                  {{{ a_rlx := 1;
                      x_rel := 1
                  ||| b_rlx := 1;
                      cas_rel_rlx(x, 1, 2) }}}
              ||| spw
                  {{{ r1 := x_rlx;
                      if r1 == 2
                      then x_rlx := 3
                      else ret 0
                      fi
                  ||| rX := x_acq;
                      rA := a_rlx;
                      rB := b_rlx;
                      ret [rX [rA rB]] }}} }}};
        ret r0_2_2 })

;; (test-->> step term_WW_WRMW_W_RRR

;;           '(0 (0 0))
;;           '(0 (0 1))
;;           '(0 (1 0))
;;           '(0 (1 1))

;;           '(1 (1 0))
;;           '(1 (1 1))
          
;;           '(2 (1 1))

;;           '(3 (0 0))
;;           '(3 (0 1))
;;           '(3 (1 0))
;;           '(3 (1 1)))

;(traces step term_WW_WRMW_W_RRR #:pp pretty-printer)

