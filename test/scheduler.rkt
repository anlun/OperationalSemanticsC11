#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../core/coreLang.rkt")
(require "../core/langs.rkt")
(require "../core/parser.rkt")
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
                               (Paths ((() 0 -1) (() 0 -1) (() 0 -1)
                                       ((L ()) 0 -1) ((R ()) 0 -1)
                                       ((L ()) 0 -1) ((R ()) 0 -1)
                                       ((L ()) 0 -1) ((R ()) 0 -1)
                                       ((L ()) 0 -1) ((R ()) 0 -1)
                                       (() 0 -1) (() 0 -1)
                                       ))
                               defaultState))
(test-->> step
          (term (,term_WrlxRrlx_WrlxRrlx startState))
          (term ((ret (0 0)) defaultState)))

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
                               (Paths ((() 0 -1) (() 0 -1) (() 0 -1)
                                       ((L ()) 0 -1) ((R ()) 0 -1)
                                       ((L ()) 0 -1)
                                       ((R ()) 0 -1) ((R ()) 0 -1)
                                       (() 0 -1) (() 0 -1)
                                       ))
                               defaultState))

(test-->>∃ step
           (term (,term_deallocate_stuck startState2))
           (term (stuck defaultState)))
