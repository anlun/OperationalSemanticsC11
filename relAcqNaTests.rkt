#lang racket
(require redex)
(require "syntax.rkt")
(require "coreUtils.rkt")
(require "etaPsiLang.rkt")
(require "relAcqRules.rkt")
(require "naRules.rkt")

(define relAcqRules (define-relAcqRules etaPsiLang synchronizeWriteFront_id
                      isReadQueueEqualTo_t))
(define naRules     (define-naRules     etaPsiLang
                      defaultState getWriteσ_nil ιNotInReadQueue_t))
(define step        (union-reduction-relations coreStep relAcqRules naRules))

#|
       c_rel = 0;
a_na  = 7; || repeat (c_acq) end;
c_rel = 1  || a_na = a_na + 1
       ret a_na

Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".

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
(test-->> step
         (term (,testTerm3 defaultState))
         (term (stuck defaultState)))
|#
; (traces step (term (,testTerm3 defaultState)))

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

(test-->>∃ step
         (term (,testTerm4 defaultState))
         (term (stuck defaultState)))

#|
Ernie Cohen's lock should work in weak memory settings.
Described in Turon-al:OOPSLA14.

                   x_rlx = 0;
                   y_rlx = 0;
x_rel = choice(1, 2);  || y_rel = choice(1, 2); 
repeat y_acq end;      || repeat x_acq end;
if x_acq == y_acq then || if x_acq != y_acq then
  a_na = 239           ||   a_na = 239


Unfortunately, DrRacket can't find fixpoint in normal time in this case.
|#
(define testTerm5
       (term (((((write rlx "x" 0) >>= (λ x
                ((write rlx "y" 0) >>= (λ x
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
                   
                  ) >>= (λ x ((read na "a") >>= (λ x (ret x)))))))))
                 () ()) ()) ())))
#|
(test-->> step
         testTerm5
         (term ((((ret 239) () ()) ()) ())))
|#
