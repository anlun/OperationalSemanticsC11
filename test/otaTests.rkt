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
(test-->>∃ step
           (term (,term_nOTA_rlx defaultState))
          
           (term ((ret 1) defaultState)))

;; (stepper step (term (,term_nOTA_rlx defaultState)) pretty-printer)

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

;; (test-->>∃ step
;;            (term (,term_nOTA_nestIf_rlx defaultState))
          
;;            (term ((ret 1) defaultState)))

;; (stepper step (term (,term_nOTA_nestIf_rlx defaultState)) pretty-printer)
