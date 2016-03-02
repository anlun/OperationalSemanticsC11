#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/parser.rkt")
(require "../steps/schedulerStep.rkt")

(define term_RCU
  @prog{cw_na    := 0;
        cr1_na   := 0;
        cr2_na   := 0;
        lhead_na := null;
        r0 := spw
              {{{ a_rlx     := [1 null];
                  ltail_rlx := a;
                  lhead_rel := a;

                  b_rlx     := [10 null];
                  rt        := ltail_rlx;
                  rtc       := rt_rlx;
                  rt_rel    := [rtc_1 b];
                  ltail_rlx := b;

                  c_rlx     := [100 null];
                  rt        := ltail_rlx;
                  rtc       := rt_rlx;
                  rt_rel    := [rtc_1 c];
                  ltail_rlx := c
              ||| r1 := spw
                        {{{ sum1_na  := 0;

                            rh      := lhead_con;
                            cur1_na := rh;                            
                            repeat
                              rCur := cur1_na;
                              if (rCur != null)
                              then rNode   := rCur_con;
                                   rSum    := sum1_na;
                                   sum1_na := rSum + rNode_1;
                                   cur1_na := rNode_2
                              else ret 0
                              fi 
                            end;
                            
                            rC := wc_acq;
                            cr1_rel := rC;

                            rh      := lhead_con;
                            cur1_na := rh;                            
                            repeat
                              rCur := cur1_na;
                              if (rCur != null)
                              then rNode   := rCur_con;
                                   rSum    := sum1_na;
                                   sum1_na := rSum + rNode_1;
                                   cur1_na := rNode_2
                              else ret 0
                              fi 
                            end;

                            sum1_na
                        ||| sum2_na  := 0;

                            rh      := lhead_con;
                            cur2_na := rh;                            
                            repeat
                              rCur := cur2_na;
                              if (rCur != null)
                              then rNode   := rCur_con;
                                   rSum    := sum2_na;
                                   sum2_na := rSum + rNode_1;
                                   cur2_na := rNode_2
                              else ret 0
                              fi 
                            end;
                            
                            rC := wc_acq;
                            cr2_rel := rC;

                            rh      := lhead_con;
                            cur2_na := rh;                            
                            repeat
                              rCur := cur2_na;
                              if (rCur != null)
                              then rNode   := rCur_con;
                                   rSum    := sum2_na;
                                   sum2_na := rSum + rNode_1;
                                   cur2_na := rNode_2
                              else ret 0
                              fi 
                            end;

                            sum2_na
                        }}};
                  ret r1
              }}};
        ret r0 })

(define-term startState
                  (updateState (Paths ())
                               (Paths ((() 0) (() 0) (() 0) (() 0) (() 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0) ((L ()) 0)
                                       ((L ()) 0)

                                       ((R ()) 0)
                                       ))
                               defaultState))

;; (test-->> step
;;           (term (,term_RCU startState))
;;           (term ((ret 0) defaultState)))
