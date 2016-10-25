#lang at-exp racket
(require redex/reduction-semantics)
;; (require redex)
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

;; (require "../core/pp.rkt")

#|
  x_rlx = 0; y_rlx = 0; z_rlx = 0;
if (x_rlx) { || if (y_rlx) {
  z_rlx = 1; ||   x_rlx = 1
  y_rlx = 1  || }
} else {     ||
  y_rlx = 1  ||
}            ||
          r = z_rlx

Possible outcome: r = 1
|#
(test-->>∃ step term_nOTA_rlx
           1)

#|
r1 = x_rlx || r2 = x_rlx || r3 = y_rlx
x_rlx = 1  || y_rlx = r2 || x_rlx = r3

In ARM it's possible to get r1 = 1.
|#
(test-->>∃ step term_nOTA_arm
           '(1 (1 1)))

;; (stepper step (term (,term_nOTA_arm defaultState)) pretty-printer)

#|
Coherence

r1 = x_rlx || x_rlx = 1
r2 = x_rlx || x_rlx = 2

It should be impossible to get r1 = 2; r1 = 1
|#
(test-->> step term_co1
          '(0 0)
          '(0 1)
          '(0 2)

          '(1 1)
          '(1 2)

          '(2 2))

#|
      x_rlx = 0; y_rlx = 0;
      z_rlx = 0; f_rlx = 0;
if (x_mod1) {  || if (y_mod3) {
  if (f_rlx) { ||   f_rlx  = 1
    z_rlx  = 1 ||   x_mod4 = 1
    y_mod2 = 1 || }
  } else {     ||
    y_mod2 = 1 || 
  }            ||
} else {       ||
  y_mod2 = 1   ||
}              ||
            r = z_rlx

Possible outcome: r = 1
|#
;; Unfortunately, this test takes forever to run.
;; Randomized testing showed that everything is fine.
;; (test-->>∃ step term_nOTA_nestIf_rlx
;;            1)

;; (stepper step (term (,term_nOTA_nestIf_rlx defaultState)) pretty-printer)

#|
  x_rlx = 0; y_rlx = 0; z_rlx = 0;
if (x_mod1) { || if (y_mod3) {
  z_rlx  = 1  ||   x_mod4 = 1
  r1 = z_rlx  ||
  y_mod2 = r1 || }
} else {      ||
  y_mod2 = 1  ||
}             ||
            r = z_rlx

Possible outcome: r = 1
|#
(test-->>∃ step term_nOTA_prop_rlx
           1)

;; (stepper step (term (,term_nOTA_prop_rlx defaultState)) pretty-printer)
