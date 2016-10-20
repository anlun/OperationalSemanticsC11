#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/langs.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

(define-term defaultState (() (Read ()) (AcqFront ()) (RelFront ()) (NA ()) (Write ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState)
   etaPsi2Lang #:domain ξ))

(define coreTest (define-coreTest coreStep defaultState))


(define rlxReadRules  (define-rlxReadRules  etaPsi2Lang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2Lang))
(define relAcqRules   (define-relAcqRules   etaPsi2Lang
                        addReadNode_t
                        are∀PostReadsRlx
                        addWriteNode_t))
(define naRules       (define-naRules       etaPsi2Lang
                        addReadNode_t
                        defaultState
                        addWriteNode_t))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules))

#|
       c_rlx = 0;
a_na  = 7; || repeat (c_rlx) end;
c_rlx = 1  || a_na = a_na + 1
       ret a_na

Example from: Vafeiadis-Narayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It uses rlx writes and reads instead of rel/acq, and it leads to `stuck`.
|#
(test-->>∃ step
         (term (,testMP+rlx defaultState))
         (term (stuck defaultState)))

#|
       c_rlx = 0;
a_rlx = 7; || if (c_acq)
c_rel = 1  ||   a_rlx = a_rlx + 1
       ret a_rlx
|#
(test-->> step
         (term (,testMP-If+rel+acq defaultState))
         (term ((ret 7) defaultState))
         (term ((ret 8) defaultState)))

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
(test-->> step
         (term (,testMP+rel+rlx+fence defaultState))
         (term ((ret 8) defaultState)))

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
(test-->> step
         (term (,testMP+rlx+fence defaultState))
         (term ((ret 8) defaultState)))

#|
An example from Vafeiadis-Narayan:OOPSLA13. It shouldn't get `stuck`.

                    lock = 1
a_na     = 2 || if ((cas_acq_rlx lock 0 1) || if ((cas_acq_rlx lock 0 1)
lock_rel = 0 ||     == 0)                  ||     == 0)
             || then                       || then
             ||    a_na = 3                ||    a_na = 2
             || else (ret -1)              || else (ret -1)
|#
(test-->> step
          (term (,testTerm9 defaultState))
          (term ((ret (-1 -1)) defaultState))
          (term ((ret (-1  2)) defaultState))
          (term ((ret ( 3 -1)) defaultState)))

#|
     x_rel = 0; y_rel = 0
x_rel = 5 || r0 = y_acq
y_rlx = 1 || r1 = x_rlx
     ret (r0 r1)

It's possible to get r0 = 1 /\ r1 = 0 in Batty-al:POPL11.
|#
(define term_Wrel0Wrlx1_Racq1Rrlx0
  @prog{x_rel := 0;
        y_rel := 0;
        r01 := spw
               {{{ x_rel := 5;
                   y_rlx := 1
               ||| r0 := y_acq;
                   r1 := x_rlx;
                   ret [r0 r1] }}};
        ret r01_2 })

(test-->>∃ step
          (term (,term_Wrel0Wrlx1_Racq1Rrlx0 defaultState))
          (term ((ret (1 0))                 defaultState)))


#|
   x_rlx = 0; a_rlx = 0
a_rlx = 5 || r0 = x_acq
x_rel = 1 || r1 = a_rlx
x_rlx = 2 ||
      ret (r0 r1) 

Release sequence example.
It should be impossible to get r0 = 2 /\ r1 = 0 according to release sequence rules.
|#
(define term_WrlxWrelWrlx_RacqRrlx
  @prog{x_rlx := 0;
        a_rlx := 0;
        r01 := spw
               {{{ a_rlx := 5;
                   x_rel := 1;
                   x_rlx := 2
               ||| r0 := x_acq;
                   r1 := a_rlx;
                   ret [r0 r1] }}};
        ret r01_2 })

(test-->> step
          (term (,term_WrlxWrelWrlx_RacqRrlx defaultState))

          (term ((ret (0 0)) defaultState))
          (term ((ret (0 5)) defaultState))

          (term ((ret (1 5)) defaultState))
          (term ((ret (2 5)) defaultState)))
