#lang at-exp racket
(require redex/reduction-semantics)
(provide (all-defined-out))
(require racket/string)
(require "../core/parser.rkt")

(define (concretize generator parameterString)
  (apply generator (string-split parameterString)))

#|
ret 5 || ret 239
|#
(define testTerm-1 (term (spw (ret 5) (ret 239))))

#|
  x_imod0 = 0; y_imod1 = 0
x_mod0  = 1 || y_mod2  = 1
R1 = y_mod1 || R2 = x_mod3
|#
(define (term_SB_abst imod0 imod1 mod0 mod1 mod2 mod3)
  @prog{x_@imod0 := 0;
        y_@imod1 := 0;
        spw
        {{{ x_@mod0 := 1;
            r1 := y_@mod1;
            ret r1
        ||| y_@mod2 := 1;
            r2 := x_@mod3;
            ret r2 }}} })

#|
  x_rlx = 0; y_rlx = 0
x_rlx  = 1 || y_rlx  = 1
R1 = y_rlx || R2 = x_rlx

Can lead to R1 = R2 = 0.
|#
(define term_WrlxRrlx_WrlxRrlx (concretize term_SB_abst "rlx rlx rlx rlx rlx rlx"))

#|
  x_rel = 0; y_rel = 0
x_rel  = 1 || y_rel = 1
R1 = y_acq || R2 = x_acq

Can lead to R1 = R2 = 0.
|#
(define term_WrelRacq_WrelRacq (concretize term_SB_abst "rel rel rel acq rel acq"))

#|
  x_rel = 0; y_rel = 0
x_sc  = 1  || y_sc  = 1
r1 = y_sc  || r2 = x_sc
       ret r1 r2
|#
(define term_WscRsc_WscRsc (concretize term_SB_abst "rel rel sc sc sc sc"))

#|
       x_rel = 0; y_rel = 0
x_{sc,rel}  = 1 || y_{sc,rel}  = 1
r1 = y_{sc,rel} || r2 = x_{sc,rel}
            ret r1 r2
|#
(define term_WrelRsc_WscRsc (concretize term_SB_abst "rel rel rel sc sc sc"))
(define term_WscRacq_WscRsc (concretize term_SB_abst "rel rel sc acq sc sc"))
(define term_WscRsc_WrelRsc (concretize term_SB_abst "rel rel sc sc rel sc"))
(define term_WscRsc_WscRacq (concretize term_SB_abst "rel rel sc sc sc acq"))

#|
   x_rlx = 0; y_rlx = 0
R1 = x_mod0 || R2 = y_mod2
y_mod1  = 1 || x_mod3  = 1
|#
(define (term_LB_abst mod0 mod1 mod2 mod3)
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r1 := x_@mod0;
            y_@mod1 := 1;
            ret r1
        ||| r2 := y_@mod2;
            x_@mod3 := 1;
            ret r2 }}} })

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(define term_RrlxWrlx_RrlxWrlx (concretize term_LB_abst "rlx rlx rlx rlx")) 

#|
R1 = x_rlx  || R2 = y_rlx
y_rel   = 1 || x_rel   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
Rel modificators solve nothing here.
|#
(define term_RrlxWrel_RrlxWrel (concretize term_LB_abst "rlx rel rlx rel"))

#|
R1 = x_acq  || R2 = y_acq
y_rlx   = 1 || x_rlx   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
Acq modificators solve nothing here.
|#
(define term_RacqWrlx_RacqWrlx (concretize term_LB_abst "acq rlx acq rlx"))


#|
R1 = x_rlx || R2 = y_rlx
y_sc   = 1 || x_sc   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
SC modificators solve nothing here.
|#
(define term_RrlxWsc_RrlxWsc (concretize term_LB_abst "rlx sc rlx sc"))

#|
R1 = x_con || R2 = y_con
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
|#
(define term_RconWrlx_RconWrlx (concretize term_LB_abst "con rlx con rlx"))

#|
R1 = x_con  || R2 = y_con
y_rel   = 1 || x_rel   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
Rel modificators solve nothing here,
because consume (con) doesn't provide synchronization.
|#
(define term_RconWrel_RconWrel (concretize term_LB_abst "con rel con rel"))

#|
R1 = x_con || R2 = y_con
y_sc   = 1 || x_sc   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
SC modificators solve nothing here,
because consume (con) doesn't provide synchronization.
|#
(define term_RconWsc_RconWsc (concretize term_LB_abst "con sc con sc"))

#|
R1 = x_acq  || R2 = y_rlx
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RacqWrel_RrlxWrel (concretize term_LB_abst "acq rel rlx rel"))

#|
R1 = x_rlx  || R2 = y_acq
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RrlxWrel_RacqWrel (concretize term_LB_abst "rlx rel acq rel"))

#|
R1 = x_acq  || R2 = y_acq
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RacqWrel_RacqWrel (concretize term_LB_abst "acq rel acq rel"))

#|
   x_rlx = 0; y_rlx = 0
R1  = x_mod0; || R2  = y_mod2;
R1' = R1 + 1; || R2' = R2 + 1;
y_mod1   = 1; || x_mod3   = 1;
ret R1'       || ret R2'
|#
(define (term_LB_abst_let mod0 mod1 mod2 mod3)
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r1  := x_@mod0;
            r11 := ret (r1 + 1);
            y_@mod1 := 1;
            ret r11
        ||| r2  := y_@mod2;
            r21 := ret (r2 + 1);
            x_@mod3 := 1;
            ret r21 }}} })

(define term_RrlxWrlx_RrlxWrlx_let (concretize term_LB_abst_let "rlx rlx rlx rlx")) 
(define term_RrlxWrel_RrlxWrel_let (concretize term_LB_abst_let "rlx rel rlx rel")) 
(define term_RrlxWsc_RrlxWsc_let   (concretize term_LB_abst_let "rlx sc  rlx sc" )) 
(define term_RconWrlx_RconWrlx_let (concretize term_LB_abst_let "con rlx con rlx")) 
(define term_RconWrel_RconWrel_let (concretize term_LB_abst_let "con rel con rel")) 
(define term_RconWsc_RconWsc_let   (concretize term_LB_abst_let "con sc  con sc" )) 
(define term_RacqWrel_RrlxWrel_let (concretize term_LB_abst_let "acq rel rlx rel"))
(define term_RrlxWrel_RacqWrel_let (concretize term_LB_abst_let "rlx rel acq rel"))
(define term_RacqWrel_RacqWrel_let (concretize term_LB_abst_let "acq rel acq rel"))

#|
     x_rlx = 0; y_rlx = 0
R1  = x_mod0; || R2  = y_mod2;
z1_rlx  = R1; || z2_rlx  = R2;
y_mod1  =  1; || x_mod3  =  1;
  r1 = z1_mod0; r2 = z2_mod0
         ret (r1  r2)
|#
(define (term_LB_abst_use mod0 mod1 mod2 mod3)
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r1  := x_@mod0;
            z1_rlx   := r1;
            y_@mod1  := 1;
            ret r1
        ||| r2  := y_@mod2;
            z2_rlx   := r2;
            x_@mod3  := 1;
            ret r2 }}};
        r1 := z1_@mod0;
        r2 := z2_@mod0;
        ret [r1 r2] })

(define term_RrlxWrlx_RrlxWrlx_use (concretize term_LB_abst_use "rlx rlx rlx rlx")) 
(define term_RrlxWrel_RrlxWrel_use (concretize term_LB_abst_use "rlx rel rlx rel")) 
(define term_RrlxWsc_RrlxWsc_use   (concretize term_LB_abst_use "rlx sc  rlx sc" )) 
(define term_RconWrlx_RconWrlx_use (concretize term_LB_abst_use "con rlx con rlx")) 
(define term_RconWrel_RconWrel_use (concretize term_LB_abst_use "con rel con rel")) 
(define term_RconWsc_RconWsc_use   (concretize term_LB_abst_use "con sc  con sc" )) 
(define term_RacqWrel_RrlxWrel_use (concretize term_LB_abst_use "acq rel rlx rel"))
(define term_RrlxWrel_RacqWrel_use (concretize term_LB_abst_use "rlx rel acq rel"))
(define term_RacqWrel_RacqWrel_use (concretize term_LB_abst_use "acq rel acq rel"))

#|
  x_mod0 = 0; y_mod0 = 0
x_mod1 = 1; || y_mod3 = 1; 
y_mod2 = 2; || x_mod4 = 2;  
 r1 = x_mod5; r2 = z2_mod5
      ret (r1 r2)

It should be possible to get r1 = r2 = 1, if there is no thread with
both release accesses. 
|#
(define (term_2+2W_abst mod0 mod1 mod2 mod3 mod4 mod5)
  @prog{x_@mod0 := 0;
        y_@mod0 := 0;
        spw
        {{{ x_@mod1 := 1;
            y_@mod2 := 2;
            ret 0
        ||| y_@mod3 := 1;
            x_@mod4 := 2;
            ret 0 }}};
        r1 := x_@mod5;
        r2 := y_@mod5;
        ret [r1 r2] })

(define term_2+2W_rlx      (concretize term_2+2W_abst "rlx rlx rlx rlx rlx rlx")) 
(define term_2+2W_rel_acq  (concretize term_2+2W_abst "rel rel rel rel rel acq")) 
(define term_2+2W_rel1_rlx (concretize term_2+2W_abst "rlx rel rlx rel rlx rlx")) 
(define term_2+2W_rel2_rlx (concretize term_2+2W_abst "rlx rlx rel rlx rel rlx")) 
(define term_2+2W_rel3_rlx (concretize term_2+2W_abst "rlx rlx rel rel rlx rlx")) 

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(define testTerm2
        @prog{spw
              {{{ x_na := 1
              ||| x_na := 2 }}} })

#|
       c_rel = 0
a_na  = 7 || repeat (c_acq) end
c_rel = 1 || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(define testMP+rel+acq ; testTerm3
  @prog{c_rel := 0;
        spw
        {{{ a_na  := 7;
            c_rel := 1
        ||| repeat c_acq end;
            r1 := a_na;
            a_na := r1 + 1 }}};
        r0 := a_na;
        ret r0 })

#|
       c_rel = 0
a_na  = 7 || repeat (c_rlx) end
c_rel = 1 || fence acq
          || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(define testMP+rel+rlx+fence
  @prog{c_rel := 0;
        spw
        {{{ a_na  := 7;
            c_rel := 1
        ||| repeat c_rlx end;
            fence acq;
            r1 := a_na;
            a_na := r1 + 1 }}};
        r0 := a_na;
        ret r0 })

#|
       c_rel = 0
a_na  = 7 || repeat (c_rlx) end
fence rel || fence acq
c_rlx = 1 || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(define testMP+rlx+fence
  @prog{c_rel := 0;
        spw
        {{{ a_na  := 7;
            fence rel;
            c_rlx := 1
        ||| repeat c_rlx end;
            fence acq;
            r1 := a_na;
            a_na := r1 + 1 }}};
        r0 := a_na;
        ret r0 })

#|
       c_rlx = 0
a_na  = 7 || repeat (c_rlx) end
c_rlx = 1 || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It uses rlx writes and reads instead of rel/acq, and it leads to `stuck`.
|#
(define testMP+rlx ; testTerm3-0
  @prog{c_rlx := 0;
        spw
        {{{ a_na  := 7;
            c_rlx := 1
        ||| repeat c_rlx end;
            r1 := a_na;
            a_na := r1 + 1 }}};
        r0 := a_na;
        ret r0 })

#|
       c_rlx = 0
a_rlx = 7 || if (c_acq)
c_rel = 1 ||   a_rlx = a_rlx + 1
       ret a_rlx
|#
(define testMP-If+rel+acq ; testTerm3-1
  @prog{c_rlx := 0;
        spw
        {{{ a_rlx := 7;
            c_rel := 1
        ||| r2 := c_acq;
            if r2
            then r1 := a_rlx;
                 a_rlx := r1 + 1
            else ret 0
            fi }}};
        r0 := a_rlx;
        ret r0 })

#|
       c_sc = 0
a_na  = 7 || repeat (c_sc) end
c_sc = 1  || a_na = a_na + 1
       ret a_na

Version with SC modifiers instead of Rel/Acq.
Example from: VafeiadisNarayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".

It shouldn't get `stuck`.
|#
(define testMP+sc ; testTerm3-2
  @prog{c_sc := 0;
        spw
        {{{ a_na := 7;
            c_sc := 1
        ||| repeat c_sc end;
            r1 := a_na;
            a_na := r1 + 1 }}};
        r0 := a_na;
        ret r0 })

#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rel = 0
               y_rel = 0
x_rel = 1          || y_rel = 1
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(define testTerm4
  @prog{x_rel := 0;
        y_rel := 0;
        spw
        {{{ x_rel := 1;
            r0 := y_acq;
            if r0 == 0
            then a_na := 239
            else ret 0
            fi
        ||| y_rel := 1;
            r1 := x_acq;
            if r1 == 0
            then a_na := 30
            else ret 0
            fi }}} })

#|
Ernie Cohen's lock should work in weak memory settings.
Described in Turon-al:OOPSLA14.

                  x_rel = 0
                  y_rel = 0
x_rel = choice(1, 2)   || y_rel = choice(1, 2) 
repeat y_acq end       || repeat x_acq end
if x_acq == y_acq then || if x_acq != y_acq then
  a_na = 239           ||   a_na = 239
|#
(define testTerm5
  @prog{x_rel := 0;
        y_rel := 0;
        spw
        {{{ x_rel := choice 1 2;
            repeat y_acq end;
            r0 := x_acq;
            r1 := y_acq;
            if r0 == r1
            then a_na := 239
            else ret 0
            fi
        ||| y_rel := choice 1 2;
            repeat x_acq end;
            r2 := x_acq;
            r3 := y_acq;
            if r2 != r3
            then a_na := 239
            else ret 0
            fi }}} })

#| CoRR_rlx (Coherence of Read-Read)
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 should be invalid.
|#
(define testTerm6
  @prog{x_rlx := 0;
        rABCD := spw
                 {{{ spw
                     {{{ x_rlx := 1
                     ||| x_rlx := 2 }}}
                 ||| spw
                     {{{ rA := x_rlx;
                         rB := x_rlx;
                         ret [rA rB]
                     ||| rC := x_rlx;
                         rD := x_rlx;
                         ret [rC rD] }}} }}};
        ret rABCD_2})

#| CoRR_rel+acq (Coherence of Read-Read)
                     x_rel = 0
x_rel = 1 || x_rel = 2 || a = x_acq || c = x_acq
          ||           || b = x_acq || d = x_acq

The execution a = d = 1 and b = c = 2 should be invalid.
|#
(define test_CoRR_rel+acq
  @prog{x_rel := 0;
        rABCD := spw
                 {{{ spw
                     {{{ x_rel := 1
                     ||| x_rel := 2 }}}
                 ||| spw
                     {{{ rA := x_acq;
                         rB := x_acq;
                         ret [rA rB]
                     ||| rC := x_acq;
                         rD := x_acq;
                         ret [rC rD] }}} }}};
        ret rABCD_2})


#|
IRIW. Anti-TSO example.

                     x_rlx = 0
                     y_rlx = 0
x_rlx = 1 || y_rlx = 1 || a = x_rlx || c = y_rlx
          ||           || b = y_rlx || d = x_rlx

The `ret ((1 0) (0 1))` shows that our model is more relaxed
than x86-TSO [Sewell-al:CACM10].
|#
(define testTerm65
  @prog{x_rlx := 0;
        y_rlx := 0;
        rABCD := spw
                 {{{ spw
                     {{{ x_rlx := 1
                     ||| y_rlx := 1 }}}
                 ||| spw
                     {{{ rA := x_rlx;
                         rB := y_rlx;
                         ret [rA rB]
                     ||| rC := y_rlx;
                         rD := x_rlx;
                         ret [rC rD] }}} }}};
        ret rABCD_2})

#|
IRIW. Anti-TSO example. (Release+Acquire)

                     x_rel = 0
                     y_rel = 0
x_rel = 1 || y_rel = 1 || a = x_acq || c = y_rel
          ||           || b = y_acq || d = x_rel

The `ret ((1 0) (0 1))` shows that our model is more relaxed
than x86-TSO [Sewell-al:CACM10].
|#
(define testTerm67
  @prog{x_rel := 0;
        y_rel := 0;
        rABCD := spw
                 {{{ spw
                     {{{ x_rel := 1
                     ||| y_rel := 1 }}}
                 ||| spw
                     {{{ rA := x_acq;
                         rB := y_acq;
                         ret [rA rB]
                     ||| rC := y_acq;
                         rD := x_acq;
                         ret [rC rD] }}} }}};
        ret rABCD_2})

#|
Anti-TSO example.
It shows why our model isn't TSO.

 x_rlx = 0; y_rlx = 0
x_rlx = 1 || a = y_rlx
y_rlx = 1 || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.

|#
(define testTerm7
  @prog{x_rlx := 0;
        y_rlx := 0;
        rAB := spw
               {{{ x_rlx := 1;
                   y_rlx := 1
               ||| rA := y_rlx;
                   rB := x_rlx;
                   ret [rA rB] }}};
        ret rAB_2})

#|
cas rlx sc "x" 1 0

Leads to `stuck` state, because Compare-and-Set (Read-Modify-Write) operations in C11 are
undefined if success modifier is weaker than fail modifier.
|#
(define testTerm8
  @prog{cas_rlx_sc(x, 1, 0)})

#|
An example from VafeiadisNarayan:OOPSLA13. It shouldn't get `stuck`.

                    lock = 1
a_na     = 2 || if ((cas_acq_rlx lock 0 1) || if ((cas_acq_rlx lock 0 1)
lock_rel = 0 ||     == 0)                  ||     == 0)
             || then                       ||
             ||    a_na = 3                ||    a_na = 2
             || else (ret -1)              || else (ret -1)
|#
(define testTerm9
  @prog{lock_rel := 1;
        r2 := spw
              {{{ a_na := 2;
                  lock_rel := 0
              ||| spw
                  {{{ r0 := cas_acq_rlx(lock, 0, 1);
                      if r0 == 0
                      then a_na := 3
                      else ret 0 - 1
                      fi
                  ||| r1 := cas_acq_rlx(lock, 0, 1);
                      if r1 == 0
                      then a_na := 2
                      else ret 0 - 1
                      fi }}} }}};
        ret r2_2})

#|
  x_rel = 0; y_rel = 0
x_rel = 5  || y_rel = 5
a_sc  = 0  || b_sc  = 0
r1 = y_acq || r2 = x_acq
       ret r1 r2

In Batty-al:POPL11 it's possible to get r1 = 0 /\ r2 = 0.
|#
(define testTerm10
  @prog{x_rel := 0;
        y_rel := 0;
        r0 := spw
              {{{ x_rel := 5;
                  a_sc  := 0;
                  r1 := y_acq;
                  ret r1
              ||| y_rel := 5;
                  b_sc  := 0;
                  r2 := x_acq;
                  ret r2 }}};
        ret r0})

#|
          x_rlx = 0; y_rlx = 0
     y_rlx = 1     || if (x_acq == 2) {
     x_rel = 1     ||    r1 = y_rlx 
x_rlx = 2 || ret 0 || } else {
                   ||    r1 = 0 }             

According to Batty-al:POPL11 it's possible to get r1 = 0, because
there is no release sequence between x_rel = 1 and x_rlx = 2.
|#
(define term_Wrel_Wrlx_Racq
  @prog{x_rlx := 0;
        y_rlx := 0;
        r0 := spw
              {{{ y_rlx := 1;
                  x_rel := 1;
                  spw
                  {{{ x_rlx := 2
                  ||| ret 0 }}}
              ||| r2 := x_acq;
                  if r2 == 2
                  then y_rlx
                  else ret 0
                  fi }}};
        ret r0_2 })

#|
      x_rel = 0
x_rel = 1 || r = x_acq
x_na  = 2 ||

Should lead to `stuck` because of VafeiadisNarayan:OOPSLA (ConsistentRFna) ---
`x_na = 2` and `r = x_acq` aren't happens-before ordered.
|#
(define term_WrelWna_Racq
  @prog{x_rel := 0;
        spw
        {{{ x_rel := 1;
            x_na  := 2
        ||| r0 := x_acq;
            ret r0 }}} })

#|
   x_rlx = 0; y_rlx = 0
R1 = x_mod0 || R2 = y_mod2
y_mod1  = 1 || x_mod3  = 1
            || x_mod4  = 2
|#
(define (abst_RW_RWW mod0 mod1 mod2 mod3 mod4)
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r1 := x_@mod0;
            y_@mod1 := 1;
            ret r1
        ||| r2 := y_@mod2;
            x_@mod3 := 1;
            x_@mod4 := 2;
            ret r2 }}} }) 

#|
   x_rlx = 0; y_rlx = 0
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1
           || x_rlx  = 2

With postponed reads it should be able to lead to R1 = 2; R1 = 1.
|#
(define term_RrlxWrlx_RrlxWrlxWrlx (concretize abst_RW_RWW "rlx rlx rlx rlx rlx")) 

#|
   x_rlx = 0; y_rlx = 0
R1 = x_acq || R2 = y_rlx
y_rlx  = 1 || x_rel  = 1
           || x_rlx  = 2

With postponed reads it shouldn't lead to R1 = 2; R1 = 1.
|#
(define term_RacqWrlx_RrlxWrelWrlx (concretize abst_RW_RWW "acq rlx rlx rel rlx")) 

#|
            x_rlx = 0; y_rlx = 0
R1 = y_mod0 || ret 0 || R2 = x_mod2 || ret 0
     x_mod1 = 1      ||      y_mod3 = 1
                ret (R1 R2)
|#
(define (abst_R-W_R-W mod0 mod1 mod2 mod3)
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r10 := spw
                   {{{ r1 := y_@mod0;
                       ret r1
                   ||| ret 0 }}};
            x_@mod1 := 1;
            ret r10_1
        ||| r20 := spw
                   {{{ r2 := x_@mod2;
                       ret r2
                   ||| ret 0 }}};
            y_@mod3 := 1;
            ret r20_1 }}} })

#|
           x_rlx = 0; y_rlx = 0
R1 = y_rlx || ret 0 || R2 = x_rlx || ret 0
     x_rlx = 1      ||      y_rlx = 1
               ret (R1 R2)
|#
(define term_Rrlx-Wrlx_Rrlx-Wrlx (concretize abst_R-W_R-W "rlx rlx rlx rlx"))

#|
           x_rlx = 0; y_rlx = 0
R1 = y_acq || ret 0 || R2 = x_acq || ret 0
     x_rlx = 1      ||      y_rlx = 1
               ret (R1 R2)
|#
(define term_Racq-Wrlx_Racq-Wrlx (concretize abst_R-W_R-W "acq rlx acq rlx"))

#|
           x_rlx = 0; y_rlx = 0
R1 = y_rlx || ret 0 || R2 = x_rlx || ret 0
     x_rel = 1      ||      y_rel = 1
               ret (R1 R2)
|#
(define term_Rrlx-Wrel_Rrlx-Wrel (concretize abst_R-W_R-W "rlx rel rlx rel"))

#|
           x_rlx = 0; y_rlx = 0
R1 = y_rlx || ret 0 || R2 = x_acq || ret 0
     x_rel = 1      ||      y_rel = 1
               ret (R1 R2)
|#
(define term_Rrlx-Wrel_Racq-Wrel (concretize abst_R-W_R-W "rlx rel acq rel"))

#|

             x_rlx = 0; y_rlx = 0
y_rlx = 1 || cas_rlx,rlx(x, 1, 2) || r1 = x_acq
x_rel = 1 ||                      || r2 = y_rlx

It's impossible to get r1 = 2; r2 = 0, due to synchronization through
RMW (cas) operation.
|#
(define term_WrlxWrel_RMWrlxrlx_RacqRrlx
  @prog{x_rlx := 0;
        y_rlx := 0;
        r012 := spw
                {{{ spw 
                    {{{ y_rlx := 1;
                        x_rel := 1
                    ||| cas_rlx_rlx(x, 1, 2)
                    }}}
                ||| r1 := x_acq;
                    r2 := y_rlx;
                    ret [r1 r2] }}};
        ret r012_2 })
  
#|
   x_rel = 0; y_rel = 1
x_mod0 = 1  || y_mod2 = 2
r1 = y_mod1 || r2 = x_mod3
       ret (r1 r2)
|#
(define (abst_W1R_W2R mod0 mod1 mod2 mod3)
  @prog{x_rel := 0;
        y_rel := 1;
        spw
        {{{ x_@mod0 := 1;
            r1 := y_@mod1;
            ret r1
        ||| y_@mod2 := 2;
            r2 := x_@mod3;
            ret r2 }}} })

(define term_W1rlxRrlx_W2rlxRrlx (concretize abst_W1R_W2R "rlx rlx rlx rlx"))
(define term_W1relRrlx_W2relRrlx (concretize abst_W1R_W2R "rel rlx rel rlx"))
(define term_W1relRacq_W2relRacq (concretize abst_W1R_W2R "rel acq rel acq"))
(define term_W1scRsc_W2relRacq   (concretize abst_W1R_W2R "sc  sc  rel acq"))
(define term_W1scRsc_W2scRacq    (concretize abst_W1R_W2R "sc  sc  sc  acq"))
(define term_W1scRsc_W2scRsc     (concretize abst_W1R_W2R "sc  sc  sc  sc "))

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
(define term_MP_pointer_consume
  @prog{data_na  := 0;
        dataP_na := 0;
        p_rel    := 0;
        r0 := spw
              {{{ data_na  := 5;
                  dataP_na := data;
                  p_rel    := dataP
              ||| r1 := p_con;
                  if r1 != 0
                  then r3 := r1_na;
                       r3_na
                  else ret 1
                  fi }}};
        ret r0_2 })

#|
WRC_rel+acq

      x_rel = 0; y_rel = 0
x_rel = 1 || r1 = x_acq || r2 = y_acq
          || y_rel = r1 || r3 = x_acq

Impossible outcome: r2 = 1 /\ r3 = 0.
|#
(define term_WRC_rel+acq
  @prog{x_rel := 0;
        y_rel := 0;
        r0 := spw
              {{{ spw
                  {{{ x_rel := 1
                  ||| r1 := x_acq;
                      y_rel := r1 }}}
              ||| r2 := y_acq;
                  r3 := x_acq;
                  ret [r2 r3] }}};
        ret r0_2})
       
#|
WRC_rlx

      x_rlx = 0; y_rlx = 0
x_rlx = 1 || r1 = x_rlx || r2 = y_rlx
          || y_rlx = r1 || r3 = x_rlx

Possible outcome: r2 = 1 /\ r3 = 0.
|#
(define term_WRC_rlx
  @prog{x_rlx := 0;
        y_rlx := 0;
        r0 := spw
              {{{ spw
                  {{{ x_rlx := 1
                  ||| r1 := x_rlx;
                      y_rlx := r1 }}}
              ||| r2 := y_rlx;
                  r3 := x_rlx;
                  ret [r2 r3] }}};
        ret r0_2})

#|
  x_rlx = 0; y_rlx = 0; z_rlx = 0;
if (x_mod1) { || if (y_mod3) {
  z_rlx  = 1  ||   x_mod4 = 1
  y_mod2 = 1  || }
} else {      ||
  y_mod2 = 1  ||
}             ||
            r = z_rlx

Possible outcome: r = 1
|#
(define (term_nOTA_abst mod0 mod1 mod2 mod3 mod4)
  @prog{x_rlx := 0;
        y_rlx := 0;
        z_rlx := 0;
        spw
        {{{ r1 := x_@mod0;
            if r1
            then z_rlx   := 1;
                 y_@mod2 := 1
            else y_@mod2 := 1
            fi
        ||| r2 := y_@mod0;
            if r2
            then x_@mod2 := 1
            else ret 0 
            fi }}};
        z_rlx })

(define term_nOTA_rlx (concretize term_nOTA_abst "rlx rlx rlx rlx rlx"))

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
(define (term_nOTA_nestIf_abst mod0 mod1 mod2 mod3 mod4)
  @prog{x_rlx := 0;
        y_rlx := 0;
        z_rlx := 0;
        f_rlx := 0;
        spw
        {{{ r1 := x_@mod0;
            if r1
            then r2 := f_rlx;
                 if r2
                 then z_rlx   := 1;
                      y_@mod2 := 1
                 else y_@mod2 := 1
                 fi
            else y_@mod2 := 1
            fi
        ||| r2 := y_@mod0;
            if r2
            then f_rlx   := 1;
                 x_@mod2 := 1
            else ret 0 
            fi }}};
        z_rlx })

(define term_nOTA_nestIf_rlx (concretize term_nOTA_nestIf_abst "rlx rlx rlx rlx rlx"))

#|
r1 = x_rlx || r2 = x_rlx || r3 = y_rlx
x_rlx = 1  || y_rlx = r2 || x_rlx = r3

In ARM it's possible to get r1 = 1.
|#
(define term_nOTA_arm
  @prog{x_rlx := 0;
        y_rlx := 0;
        spw
        {{{ r1 := x_rlx;
            x_rlx := 1;
            ret r1
        ||| spw
            {{{ r2 := x_rlx;
                y_rlx := r2
            ||| r3 := y_rlx;
                x_rlx := r3
            }}} }}} })

#|
Coherence

r1 = x_rlx || x_rlx = 1
r2 = x_rlx || x_rlx = 2

It should be impossible to get r1 = 2; r1 = 1
|#
(define term_co1
  @prog{x_rlx := 0;
        r0 := spw
              {{{ r1 := x_rlx;
                  r2 := x_rlx;
                  ret [r1 r2]
              ||| x_rlx := 1;
                  x_rlx := 2  }}};
        ret r0_1 })

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
(define (term_nOTA_prop_abst mod0 mod1 mod2 mod3 mod4)
  @prog{x_rlx := 0;
        y_rlx := 0;
        z_rlx := 0;
        spw
        {{{ r1 := x_@mod0;
            if r1
            then z_rlx   := 1;
                 r3      := z_rlx;
                 y_@mod2 := r3
            else y_@mod2 := 1
            fi
        ||| r2 := y_@mod0;
            if r2
            then x_@mod2 := 1
            else ret 0 
            fi }}};
        z_rlx })

(define term_nOTA_prop_rlx (concretize term_nOTA_prop_abst "rlx rlx rlx rlx rlx"))

#|
               x_rlx := 0; y_rlx := 0;
x_rlx := 1 || x_rlx := 2 || r1 = x_rlx; || repeat y_acq end;
           ||            || r2 = x_rlx; || r4 = x_rlx
           ||            || y_rel := 1  ||
                       r5 = x_rlx 
                   ret [[r1 r2] [r3 r4]] r5
Because of read-read coherence, if r3 == 1 then r4 value has to be not
older than r2.
|#
(define term_CoRR_spec
  @prog{x_rlx := 0;
        y_rlx := 0;
        r0 := spw
              {{{ spw {{{ x_rlx := 1 ||| x_rlx := 2 }}}
              ||| spw
                  {{{ r1 := x_rlx;
                      r2 := x_rlx;
                      y_rel := 1;
                      ret [r1 r2]
                  ||| repeat y_acq end;
                      r4 := x_rlx;
                      ret r4
                  }}}
              }}};
        r5 := x_rlx;
        ret [r0_2 r5] })

#|
   x_imod = 0; y_imod = 0
x_wmod1  = 1 || y_wmod2  = 1
fence fmod1  || fence fmod2
r1 = x_rmod1 || r2 = y_rmod2
        ret (r1, r2)
|#
(define (term_SB+fences_abst imod wmod1 wmod2 fmod1 fmod2 rmod1 rmod2)
  @prog{x_@imod := 0;
        y_@imod := 0;
        spw
        {{{ x_@wmod1 := 1;
            fence @fmod1;
            y_@rmod1
        ||| y_@wmod2 := 1;
            fence @fmod2;
            x_@rmod2
        }}} })


#|
     x_rel = 0; y_rel = 0;
x_rel = 1     || y_rel = 1
fence_sc      || fence_sc
r1 = y_acq    || r2 = x_acq
        ret (r1, r2)

r1 = 0, r2 = 0 - is not allowed
|#
(define testSB+rel+acq+fences+sc (concretize term_SB+fences_abst  "rel rel rel sc sc acq acq"))

#|
  x_rlx = 0; y_rlx = 0;
x_rlx = 1  || y_rlx = 1
fence sc   || fence sc
r1 = y_rlx || r2 = x_rlx 
       ret (r1, r2)

r1 = 0, r2 = 0 - is not allowed
|#
(define testSB+rlx+fences+sc (concretize term_SB+fences_abst  "rlx rlx rlx sc sc rlx rlx"))

#|
         x_rlx = 0; y_rlx = 0;
x_rlx = 1         || y_rlx = 1
fence sc          || fence sc
r1 = cas(y, 0, 2) || r2 = cas(x, 0, 2)
       ret (r1, r2)

r1 = 2, r2 = 2 - is not allowed
|#
(define testSB+cas+rel+acq+fences
  @prog{x_rlx := 0;
        y_rlx := 0; 
        spw
        {{{ x_rlx := 1;
            fence sc;
            cas_rlx_rlx(y, 0, 2)      
        ||| y_rlx := 1;
            fence sc;
            cas_rlx_rlx(x, 0, 2)
        }}} })
