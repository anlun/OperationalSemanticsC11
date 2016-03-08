#lang at-exp racket
(require redex/reduction-semantics)
;; (require redex)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../core/coreLang.rkt")
(require "../core/langs.rkt")
(require "../core/parser.rkt")
(require "../core/pp.rkt")
(require "testTerms.rkt")
(require "../steps/schedulerStep.rkt")

#|
  x_rlx = 0; y_rlx = 0
x_rlx  = 1 || y_rlx  = 1
R1 = y_rlx || R2 = x_rlx

Can lead to R1 = R2 = 0.
|#
(define-term startState
                  (updateState (Paths ())
                               (Paths ((() 0 None) (() 0 None) (() 0 None)
                                       ((L ()) 0 None) ((R ()) 0 None)
                                       ((L ()) 0 None) ((R ()) 0 None)
                                       ((L ()) 0 None) ((R ()) 0 None)
                                       ((L ()) 0 None) ((R ()) 0 None)
                                       (() 0 None) (() 0 None)
                                       ))
                               defaultState))
;; (test-->> step
;;           ;; (term (,term_WrlxRrlx_WrlxRrlx startState))
;;           (term (,term_WrlxRrlx_WrlxRrlx defaultState))
;;           (term ((ret (0 0)) defaultState)))

;; (stepper step (term (,term_WrlxRrlx_WrlxRrlx defaultState)) pretty-printer)
;; (stepper step (term (,term_WrlxRrlx_WrlxRrlx defaultState)))

(define term_deallocate_stuck
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ x_rlx := 1;
            dealloc x
        ||| y_rlx := 1;
            x_rlx
        }}} })

(define-term startState2
                  (updateState (Paths ())
                               (Paths ((() 0 None) (() 0 None) (() 0 None)
                                       ((L ()) 0 None) ((R ()) 0 None)
                                       ((L ()) 0 None)
                                       ((R ()) 0 None) ((R ()) 0 None)
                                       (() 0 None) (() 0 None)
                                       ))
                               defaultState))

;; (test-->>∃ step
;;            (term (,term_deallocate_stuck defaultState))
;;            ;; (term (,term_deallocate_stuck startState2))
;;            (term (stuck defaultState)))
