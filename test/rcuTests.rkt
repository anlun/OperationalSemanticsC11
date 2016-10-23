#lang at-exp racket
(require redex/reduction-semantics)
;; (require redex)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/parser.rkt")
(require "../core/pp.rkt")
(require "../steps/relAcqNaRlxPost.rkt")

(define term_RCU
  @prog{cw_na    := 0;
        cr1_na   := 0;
        cr2_na   := 0;
        lhead_na := null;
        spw
        {{{ ;; Adds to list the first value (1).
            a_rlx     := [1 null];
            ltail_na  := a;
            lhead_rel := a;

            ;; Adds to list the second value (10).
            b_rlx     := [10 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rel    := [rtc_1 b];
            ltail_na := b;

            ;; Adds to list the second value (100).
            c_rlx     := [100 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rel    := [rtc_1 c];
            ltail_na := c;
            
            ;; Update second list element.           
            r1  := lhead_rlx; ;; r1 -> lhead
            r1c := r1_rlx;
            r2  := ret r1c_2;     ;; r2 -> the second element
            r2c := r2_rlx;
            r3  := ret r2c_2;     ;; r3 -> the third element
            
            d_rel  := [1000 r3];
            r1_rel := [r1c_1 d];

            rcw    := cw_rlx;
            rcwn   := ret rcw + 2;
            cw_rel := rcwn;
            
            counter_rlx := 0;
            repeat
              rcr1 := cr1_acq;
              ret (rcr1 >= rcwn)
            end;
            repeat
              rcr2 := cr2_acq;
              ret (rcr2 >= rcwn)
            end;
            dealloc r2;

            ret 0
        ||| spw
            {{{ sum11_na  := 0;

                ;; Starting working with the list.
                rC := cw_acq;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh; 
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum11_na;
                       rVal    := ret rNode_1;
                       sum11_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                            
                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rel := rC;
                
                sum12_na  := 0;
                ;; Starting working with the list.
                rC := cw_acq;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh;                            
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum12_na;
                       rVal    := ret rNode_1;
                       sum12_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rel := rC;

                r11 := sum11_na;
                r12 := sum12_na;
                ret [r11 r12]
            ||| sum21_na  := 0;

                ;; Starting working with the list.
                rC := cw_acq;
                cr2_rlx := rC + 1;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum21_na;
                       rVal    := ret rNode_1;
                       sum21_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                      
                rC := cw_rlx;
                cr2_rel := rC;
                
                sum22_na := 0;
                ;; Starting working with the list.
                rC := cw_acq;
                cr2_rlx := rC + 1;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum22_na;
                       rVal    := ret rNode_1;
                       sum22_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                rC := cw_rlx;
                cr2_rel := rC;

                r21 := sum21_na;
                r22 := sum22_na;
                ret [r21 r22]
            }}}
       }}} })

(define (rcuTest)
  (test-->> randomStep term_RCU
            (term (ret (0 (0 0))))))

;; Usage of consume reads leads to stuck states, because the data-dependency relation
;; doesn't go beyond write-read combination of cur(1|2) in repeat loops.
;; If we change them to acquire reads, everything works fine.

;; (traces randomStep (term (,term_RCU defaultState)) #:pp pretty-printer)
;; (stepper randomStep (term (,term_RCU defaultState)) pretty-printer)

(define term_RCU_rlx
  @prog{cw_na    := 0;
        cr1_na   := 0;
        cr2_na   := 0;
        lhead_na := null;
        spw
        {{{ ;; Adds to list the first value (1).
            a_rlx     := [1 null];
            ltail_na := a;
            lhead_rlx := a;

            ;; Adds to list the second value (10).
            b_rlx     := [10 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rlx    := [rtc_1 b];
            ltail_na := b;

            ;; Adds to list the second value (100).
            c_rlx     := [100 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rlx    := [rtc_1 c];
            ltail_na := c;
            
            ;; Update second list element.           
            r1  := lhead_rlx; ;; r1 -> lhead
            r1c := r1_rlx;
            r2  := ret r1c_2;     ;; r2 -> the second element
            r2c := r2_rlx;
            r3  := ret r2c_2;     ;; r3 -> the third element
            
            d_rlx  := [1000 r3];
            r1_rlx := [r1c_1 d];

            rcw    := cw_rlx;
            cw_rlx := rcw + 2;
            iterCounter_na := 0;
            ;; repeat
            ;;   ric := iterCounter_na;
            ;;   iterCounter_na := ric + 1;
            ;;   rcr1 := cr1_acq;
            ;;   ret (rcr1 % 2)
            ;; end;
            ;; repeat
            ;;   ric := iterCounter_na;
            ;;   iterCounter_na := ric + 1;
            ;;   rcr2 := cr2_acq;
            ;;   ret (rcr2 % 2)
            ;; end;
            ;; dealloc r2;

            ret 0
        ||| spw
            {{{ sum11_na  := 0;

                ;; Starting working with the list.
                rC := cw_rlx;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_rlx;
                cur1_na := rh; 
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_rlx;
                       rSum    := sum11_na;
                       rVal    := ret rNode_1;
                       sum11_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                            
                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rlx := rC;
                
                sum12_na  := 0;
                ;; Starting working with the list.
                rC := cw_rlx;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_rlx;
                cur1_na := rh;                            
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_rlx;
                       rSum    := sum12_na;
                       rVal    := ret rNode_1;
                       sum12_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rlx := rC;

                r11 := sum11_na;
                r12 := sum12_na;
                ret [r11 r12]
            ||| sum21_na  := 0;

                ;; Starting working with the list.
                rC := cw_rlx;
                cr2_rlx := rC + 1;

                rh      := lhead_rlx;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_rlx;
                       rSum    := sum21_na;
                       rVal    := ret rNode_1;
                       sum21_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                      
                rC := cw_rlx;
                cr2_rlx := rC;
                
                sum22_na := 0;
                ;; Starting working with the list.
                rC := cw_rlx;
                cr2_rlx := rC + 1;

                rh      := lhead_rlx;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_rlx;
                       rSum    := sum22_na;
                       rVal    := ret rNode_1;
                       sum22_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                rC := cw_rlx;
                cr2_rlx := rC;

                r21 := sum21_na;
                r22 := sum22_na;
                ret [r21 r22]
            }}}
       }}} })

(define (rcuTestRlx)
  (test-->> randomStep term_RCU_rlx
            (term (ret (0 (0 0))))))

(define term_RCU_less_rlx
  @prog{cw_na    := 0;
        cr1_na   := 0;
        cr2_na   := 0;
        lhead_na := null;
        spw
        {{{ ;; Adds to list the first value (1).
            a_rlx     := [1 null];
            ltail_na := a;
            lhead_rel := a;

            ;; Adds to list the second value (10).
            b_rlx     := [10 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rlx    := [rtc_1 b];
            ltail_na := b;

            ;; Adds to list the second value (100).
            c_rlx     := [100 null];
            rt        := ltail_na;
            rtc       := rt_rlx;
            rt_rlx    := [rtc_1 c];
            ltail_na := c;
            
            ;; Update second list element.           
            r1  := lhead_rlx; ;; r1 -> lhead
            r1c := r1_rlx;
            r2  := ret r1c_2;     ;; r2 -> the second element
            r2c := r2_rlx;
            r3  := ret r2c_2;     ;; r3 -> the third element
            
            d_rel  := [1000 r3];
            r1_rlx := [r1c_1 d];

            rcw    := cw_rlx;
            cw_rel := rcw + 2;
            iterCounter_na := 0;
            ;; repeat
            ;;   ric := iterCounter_na;
            ;;   iterCounter_na := ric + 1;
            ;;   rcr1 := cr1_acq;
            ;;   ret (rcr1 % 2)
            ;; end;
            ;; repeat
            ;;   ric := iterCounter_na;
            ;;   iterCounter_na := ric + 1;
            ;;   rcr2 := cr2_acq;
            ;;   ret (rcr2 % 2)
            ;; end;
            ;; dealloc r2;

            ret 0
        ||| spw
            {{{ sum11_na  := 0;

                ;; Starting working with the list.
                rC := cw_acq;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh; 
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum11_na;
                       rVal    := ret rNode_1;
                       sum11_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                            
                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rel := rC;
                
                sum12_na  := 0;
                ;; Starting working with the list.
                rC := cw_acq;
                cr1_rlx := rC + 1;

                ;; Traversing the list.
                rh      := lhead_acq;
                cur1_na := rh;                            
                repeat
                  rCur := cur1_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum12_na;
                       rVal    := ret rNode_1;
                       sum12_na := rVal + rSum;
                       cur1_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                ;; A signalization of a RCU quiescent state.
                rC := cw_rlx;
                cr1_rel := rC;

                r11 := sum11_na;
                r12 := sum12_na;
                ret [r11 r12]
            ||| sum21_na  := 0;

                ;; Starting working with the list.
                rC := cw_acq;
                cr2_rlx := rC + 1;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum21_na;
                       rVal    := ret rNode_1;
                       sum21_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;
                      
                rC := cw_rlx;
                cr2_rel := rC;
                
                sum22_na := 0;
                ;; Starting working with the list.
                rC := cw_acq;
                cr2_rlx := rC + 1;

                rh      := lhead_acq;
                cur2_na := rh;                            
                repeat
                  rCur := cur2_na;
                  if (rCur != null)
                  then rNode   := rCur_acq;
                       rSum    := sum22_na;
                       rVal    := ret rNode_1;
                       sum22_na := rVal + rSum;
                       cur2_na := rNode_2;
                       ret 0
                  else ret 1
                  fi 
                end;

                rC := cw_rlx;
                cr2_rel := rC;

                r21 := sum21_na;
                r22 := sum22_na;
                ret [r21 r22]
            }}}
       }}} })


(define (rcuTestLessRlx)
  (test-->> randomStep term_RCU_less_rlx
            (term (ret (0 (0 0))))))
