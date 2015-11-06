#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

#|
ret 5 || ret 239
|#
(define testTerm-1 (term (spw (ret 5) (ret 239))))

#|
  x_imod0 = 0; y_imod1 = 0
y_mod0  = 1 || x_mod2  = 1
R1 = x_mod1 || R2 = y_mod3
|#
(define (term_WR_WR_gen imod0 imod1 mod0 mod1 mod2 mod3)
  (term
   ((write ,imod0 "x" 0) >>= (λ z
   ((write ,imod1 "y" 0) >>= (λ z
   ((spw
     ((write ,mod0 "y" 1) >>= (λ z
     ((read  ,mod1 "x")   >>= (λ x
      (ret x)))))
     ((write ,mod2 "x" 1) >>= (λ z
     ((read  ,mod3 "y")   >>= (λ y
      (ret y))))))
   >>=
   (λ z (ret z)))))))))

#|
  x_rlx = 0; y_rlx = 0
y_rlx  = 1 || x_rlx  = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(define term_WrlxRrlx_WrlxRrlx (term_WR_WR_gen 'rlx 'rlx 'rlx 'rlx 'rlx 'rlx))

#|
  x_rel = 0; y_rel = 0
y_rel  = 1 || x_rel = 1
R1 = x_acq || R2 = y_acq

Can lead to R1 = R2 = 0.
|#
(define term_WrelRacq_WrelRacq (term_WR_WR_gen 'rel 'rel 'rel 'acq 'rel 'acq))

#|
  x_rel = 0; y_rel = 0
x_sc  = 1  || y_sc  = 1
r1 = y_sc  || r2 = x_sc
       ret r1 r2
|#
(define term_WscRsc_WscRsc (term_WR_WR_gen 'rel 'rel 'sc 'sc 'sc 'sc))

#|
       x_rel = 0; y_rel = 0
x_{sc,rel}  = 1 || y_{sc,rel}  = 1
r1 = y_{sc,rel} || r2 = x_{sc,rel}
            ret r1 r2
|#
(define term_WrelRsc_WscRsc (term_WR_WR_gen 'rel 'rel 'rel 'sc 'sc 'sc))
(define term_WscRacq_WscRsc (term_WR_WR_gen 'rel 'rel 'sc 'acq 'sc 'sc))
(define term_WscRsc_WrelRsc (term_WR_WR_gen 'rel 'rel 'sc 'sc 'rel 'sc))
(define term_WscRsc_WscRacq (term_WR_WR_gen 'rel 'rel 'sc 'sc 'sc 'acq))

#|
   x_rlx = 0; y_rlx = 0;
R1 = x_mod0 || R2 = y_mod2
y_mod1  = 1 || x_mod3  = 1
|#
(define (term_RW_RW_gen mod0 mod1 mod2 mod3)
  (term
   ((write rlx "x" 0) >>= (λ z
   ((write rlx "y" 0) >>= (λ z
   ((spw
     ((read  ,mod0 "x")   >>= (λ x
     ((write ,mod1 "y" 1) >>= (λ z
      (ret x)))))
     ((read  ,mod2 "y")   >>= (λ y
     ((write ,mod3 "x" 1) >>= (λ z
      (ret y))))))
     >>=
     (λ x (ret x)))))))))


#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(define term_RrlxWrlx_RrlxWrlx (term_RW_RW_gen 'rlx 'rlx 'rlx 'rlx)) 

#|
R1 = x_rlx  || R2 = y_rlx
y_rel   = 1 || x_rel   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
Rel modificators solve nothing here.
|#
(define term_RrlxWrel_RrlxWrel (term_RW_RW_gen 'rlx 'rel 'rlx 'rel))

#|
R1 = x_acq  || R2 = y_rlx
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RacqWrel_RrlxWrel (term_RW_RW_gen 'acq 'rel 'rlx 'rel))

#|
R1 = x_rlx  || R2 = y_acq
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RrlxWrel_RacqWrel (term_RW_RW_gen 'rlx 'rel 'acq 'rel))

#|
R1 = x_acq  || R2 = y_acq
y_rel   = 1 || x_rel   = 1

It's impossible to get R1 = R2 = 1.
|#
(define term_RacqWrel_RacqWrel (term_RW_RW_gen 'acq 'rel 'acq 'rel))

#|
R1 = x_rlx || R2 = y_rlx
y_sc   = 1 || x_sc   = 1

With postponed reads it should be able to lead to R1 = R2 = 1. 
SC modificators solve nothing here.
|#
(define term_RrlxWsc_RrlxWsc (term_RW_RW_gen 'rlx 'sc 'rlx 'sc))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(define testTerm2
        (term (spw (write na "x" 1)
                   (write na "x" 2))))

#|
       c_rel = 0;
a_na  = 7; || repeat (c_acq) end;
c_rel = 1  || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(define testTerm3
         (term (((write rel "c" 0) >>= (λ x
                    (spw
                     ((write na  "a" 7) >>= (λ x
                      (write rel "c" 1)))
                     ((repeat (read acq "c")) >>= (λ x
                     ((read  na "a") >>= (λ x
                      (write na "a" (+ 1 x))))
                      ))
                    )))
                    >>= (λ x (read na "a")))))

#|
       c_rlx = 0;
a_na  = 7; || repeat (c_rlx) end;
c_rlx = 1  || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It uses rlx writes and reads instead of rel/acq, and it leads to `stuck`.
|#
(define testTerm3-0
         (term (((write rlx "c" 0) >>= (λ x
                    (spw
                     ((write na  "a" 7) >>= (λ x
                      (write rlx "c" 1)))
                     ((repeat (read rlx "c")) >>= (λ x
                     ((read  na "a") >>= (λ x
                      (write na "a" (+ 1 x))))
                      ))
                    )))
                    >>= (λ x (read na "a")))))

#|
       c_rlx = 0;
a_rlx = 7; || if (c_acq)
c_rel = 1  ||   a_rlx = a_rlx + 1
       ret a_rlx
|#
(define testTerm3-1
         (term (((write rlx "c" 0) >>= (λ x
                    (spw
                     ((write rlx "a" 7) >>= (λ x
                      (write rel "c" 1)))
                     ((read acq "c") >>= (λ cond
                     (if cond
                       ((read  rlx "a") >>= (λ x
                        (write rlx "a" (+ 1 x))))
                       (ret 0))
                      ))
                    )))
                    >>= (λ x (read rlx "a")))))

#|
       c_sc = 0;
a_na  = 7; || repeat (c_sc) end;
c_sc = 1   || a_na = a_na + 1
       ret a_na

Version with SC modifiers instead of Rel/Acq.
Example from: VafeiadisNarayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".

It shouldn't get `stuck`.
|#
(define testTerm3-2
         (term (((write sc "c" 0) >>= (λ x
                    (spw
                     ((write na "a" 7) >>= (λ x
                      (write sc "c" 1)))
                     ((repeat (read sc "c")) >>= (λ x
                     ((read  na "a") >>= (λ x
                      (write na "a" (+ 1 x))))
                      ))
                    )))
                    >>= (λ x (read na "a")))))

#|
         f_rel = 0;
         d_na  = 0'
d_na  = 239; || repeat (f_acq) end;
f_rel = 1    || r1 = d_na
           ret r1

Example from: Vafeiadis-Narayan:OOPSLA13
"Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It shouldn't get `stuck`.
|#
(define testTerm3-3
         (term (((write rel "f" 0) >>= (λ x
                ((write rel "d" 0) >>= (λ x
                    (spw
                     ((write na  "d" 239) >>= (λ x
                      (write rel "f" 1)))
                     ((repeat (read acq "f")) >>= (λ x
                      (read  na "d"))))))))
                    >>= (λ x (ret (proj2 x))))))


#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rel = 0;
               y_rel = 0;
x_rel = 1;         || y_rel = 1;
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(define testTerm4
            (term ((write rel "x" 0) >>= (λ x
                  ((write rel "y" 0) >>= (λ x
                   (spw
                    ((write rel "x" 1) >>= (λ x
                    ((read  acq "y"  ) >>= (λ y
                     (if (== 0 y) (write na "a" 239) (ret 0))))))
                    ((write rel "y" 1) >>= (λ x
                    ((read  acq "x"  ) >>= (λ x
                     (if (== 0 x) (write na "a" 30 ) (ret 0))))))
                    )
                    )) ))))


#|
Ernie Cohen's lock should work in weak memory settings.
Described in Turon-al:OOPSLA14.

                   x_rel = 0;
                   y_rel = 0;
x_rel = choice(1, 2);  || y_rel = choice(1, 2); 
repeat y_acq end;      || repeat x_acq end;
if x_acq == y_acq then || if x_acq != y_acq then
  a_na = 239           ||   a_na = 239

Unfortunately, DrRacket can't find fixpoint in normal time in this case.
|#
(define testTerm5
          (term ((write rel "x" 0) >>= (λ x
                ((write rel "y" 0) >>= (λ x
                ((spw
                   ((write rel "x" (choice 1 2))  >>= (λ x
                   ((repeatFuel 1 (read acq "y")) >>= (λ x
                   ((read acq "x") >>= (λ x
                   ((read acq "y") >>= (λ y
                    (if (== x y) (write na "a" 239) (ret 0))))))))))

                   ((write rel "y" (choice 1 2))  >>= (λ x
                   ((repeatFuel 1 (read acq "x")) >>= (λ x
                   ((read acq "x") >>= (λ x
                   ((read acq "y") >>= (λ y
                    (if (!= x y) (write na "a" 239) (ret 0))))))))))
                   
                  ) >>= (λ x ((read na "a") >>= (λ x (ret x)))))))))))


#|
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 should be invalid.
|#
(define testTerm6
           (term ((write rlx "x" 0) >>= (λ x
                 ((spw
                   (spw
                    (write rlx "x" 1)
                    (write rlx "x" 2))
                   (spw
                    ((read rlx "x") >>= (λ a
                    ((read rlx "x") >>= (λ b (ret (a b))))))

                    ((read rlx "x") >>= (λ c
                    ((read rlx "x") >>= (λ d (ret (c d))))))                    
                    )) >>= (λ x
                 (ret (proj2 x))))))))

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
           (term ((write rlx "x" 0) >>= (λ x
                 ((write rlx "y" 0) >>= (λ x
                 ((spw
                   (spw
                    (write rlx "x" 1)
                    (write rlx "y" 1))
                   (spw
                    ((read rlx "x") >>= (λ a
                    ((read rlx "y") >>= (λ b (ret (a b))))))

                    ((read rlx "y") >>= (λ c
                    ((read rlx "x") >>= (λ d (ret (c d))))))                    
                    )) >>= (λ x
                 (ret (proj2 x))))))))))

#|
Anti-TSO example.
It shows why our model isn't TSO.

     x = 0; y = 0
x_rlx = 1 || a = y_rlx
y_rlx = 1 || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.
|#
(define testTerm7
     (term ((write rlx "x" 0) >>= (λ x
           ((write rlx "y" 0) >>= (λ x
           ((spw
            ((write rlx "x" 1) >>= (λ x
             (write rlx "y" 1)))
            ((read rlx "y") >>= (λ a
            ((read rlx "x") >>= (λ b
             (ret (a b))))))
            ) >>= (λ x
            (ret (proj2 x))))))))))

#|
cas rlx sc "x" 1 0

Leads to `stuck` state, because Compare-and-Set (Read-Modify-Write) operations in C11 are
undefined if success modifier is weaker than fail modifier.
|#
(define testTerm8
  (term (cas rlx sc "x" 1 0)))

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
     (term ((write rel "lock" 1) >>= (λ x
            (spw
             ((write na "a" 2) >>= (λ x
              (write rel "lock" 0)))
             (spw
              ((cas acq rlx "lock" 0 1) >>= (λ x
               (if (== x 0)
                   (write na "a" 3)
                   (ret -1))))
              ((cas acq rlx "lock" 0 1) >>= (λ x
               (if (== x 0)
                   (write na "a" 2)
                   (ret -1))))
              ))))))

#|
  x_rel = 0; y_rel = 0
x_rel = 5  || y_rel = 5
a_sc  = 0  || b_sc  = 0
r1 = y_acq || r2 = x_acq
       ret r1 r2

In Batty-al:POPL11 it's possible to get r1 = 0 /\ r2 = 0.
|#
(define testTerm10
  (term ((write rel "x" 0) >>= (λ r
        ((write rel "y" 0) >>= (λ r
        (spw ((write rel "x" 5) >>= (λ r
             ((write sc  "a" 0) >>= (λ r
              (read  acq "y")))))
             ((write rel "y" 5) >>= (λ r
             ((write sc  "b" 0) >>= (λ r
              (read  acq "x"))))))))))))

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
  (term ((write rlx "x" 0) >>= (λ r
        ((write rlx "y" 0) >>= (λ r
        ((spw ((write rlx "y" 1) >>= (λ r
              ((write rel "x" 1) >>= (λ r
               (spw (write rlx "x" 2)
                    (ret 0))))))
              ((read acq "x") >>= (λ v
               (if v (read rlx "y")
                     (ret 1)))))
        >>= (λ r (ret (proj2 r))))))))))

#|
(test-->> step
         (term (,testTerm5 etaPsiDefaultState))
         (term ((ret 239) deafultState)))
|#

#|
      x_rel = 0
x_rel = 1 || r = x_acq
x_na  = 2 ||

Should lead to `stuck` because of VafeiadisNarayan:OOPSLA (ConsistentRFna) ---
`x_na = 2` and `r = x_acq` aren't happens-before ordered.
|#
(define term_WrelWna_Racq
  (term ((write rel "x" 0) >>= (λ r
         (spw ((write rel "x" 1) >>= (λ r
               (write na  "x" 2)))
              (read acq "x"))))))

