#lang at-exp racket
(require redex/reduction-semantics)
;; (require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/parser.rkt")
(require "../core/pp.rkt")
(require "../steps/schedulerStep.rkt")

(define term_RCU
  @prog{cw_na    := 0;
        cr1_na   := 0;
        cr2_na   := 0;
        lhead_na := null;
        spw
        {{{ ;; Adds to list the first value (1).
            a_rlx     := [1 null];
            ltail_rlx := a;
            lhead_rel := a;

            ;; Adds to list the second value (10).
            b_rlx     := [10 null];
            rt        := ltail_rlx;
            rtc       := rt_rlx;
            rt_rel    := [rtc_1 b];
            ltail_rlx := b;

            ;; Adds to list the second value (100).
            c_rlx     := [100 null];
            rt        := ltail_rlx;
            rtc       := rt_rlx;
            rt_rel    := [rtc_1 c];
            ltail_rlx := c;
                  
            ;; rt  := lhead_rlx;
            ;; rtc := rt_rlx;
            ;; rt  := ret rtc_2;
            ret 0
        ||| spw
            {{{ sum1_na  := 0;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh; 
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum1_na;
                       rVal    := ret rNode_1;
                       sum1_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                            
                ;; A signalization of a RCU quiescent state.
                rC := cw_acq;
                cr1_rel := rC;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh;                            
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum1_na;
                       rVal    := ret rNode_1;
                       sum1_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                sum1_na
            ||| sum2_na  := 0;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum2_na;
                       rVal    := ret rNode_1;
                       sum2_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                      
                rC := cw_acq;
                cr2_rel := rC;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum2_na;
                       rVal    := ret rNode_1;
                       sum2_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                sum2_na
            }}}
       }}} })

(define-term startState
                  (updateState (Paths ())
                               (Paths ((() 0 None) (() 0 None) (() 0 None) (() 0 None) (() 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None) ((L ()) 0 None)
                                       ((L ()) 0 None)

                                       ((R ()) 0 None)
                                       ))
                               defaultState))

(test-->> step
          ;; (term (,term_RCU startState))
          (term (,term_RCU defaultState))
          (term ((ret (0 (0 0))) defaultState)))

;; Usage of consume reads leads to stuck states, because the data-dependency relation
;; doesn't go beyond write-read combination of cur(1|2) in repeat loops.
;; If we change them to acquire reads, everything works fine.

;; (traces step (term (,term_RCU defaultState)) #:pp pretty-printer)
;; (stepper step (term (,term_RCU defaultState)) pretty-printer)
