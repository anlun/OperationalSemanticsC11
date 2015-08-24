#lang racket
(require redex)
(require "syntax.rkt")
(require "coreUtils.rkt")
(require "etaPsi2Lang.rkt")
(require "rlxRules.rkt")
(require "relAcqRules.rkt")
(require "naRules.rkt")

(define rlxReadRules  (define-rlxReadRules  etaPsi2Lang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2Lang
                        getWriteσ_2ψ isReadQueueEqualTo_t ιNotInReadQueue_t))
(define relAcqRules   (define-relAcqRules   etaPsi2Lang synchronizeWriteFront
                        isReadQueueEqualTo_t))
(define naRules       (define-naRules       etaPsi2Lang
                        defaultState getWriteσ_2ψ ιNotInReadQueue_t))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules))

#|
       c_rlx = 0;
a_na  = 7; || repeat (c_rlx) end;
c_rlx = 1  || a_na = a_na + 1
       ret a_na

Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".
It uses rlx writes and reads instead of rel/acq, and it leads to `stuck`.
|#
(define testTerm3
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

(test-->>∃ step
         (term (,testTerm3 defaultState))
         (term (stuck defaultState)))

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

(test-->> step
         (term (,testTerm3-1 defaultState))
         (term ((ret 7) defaultState))
         (term ((ret 8) defaultState)))

#|
An example from VafeiadisNarayan:OOPSLA13. It shouldn't get `stuck`.

                    lock = 1
a_na     = 2 || if (cas_acq_rlx lock 0 1) then || if (cas_acq_rlx lock 0 1)
lock_rel = 0 ||    a_na = 3                    ||    a_na = 2
                    ret a
|#

(define testTerm9
    (term (((write rlx "lock" 1) >>= (λ x
            (spw
             ((write na "a" 2) >>= (λ x
              (write rel "lock" 0)))
             (spw
              ((cas acq rlx "lock" 0 1) >>= (λ x
               (if x
                   (write na "a" 3)
                   (ret -1))))
              ((cas acq rlx "lock" 0 1) >>= (λ x
               (if x
                   (write na "a" 2)
                   (ret -1))))
              ))))
            defaultState)))

#|
  actual: '((ret (0 (-1 -1))) (() (Read ()) (Write ())))
  actual: '((ret (0 (-1 0))) (() (Read ()) (Write ())))
  actual: '((ret (0 (0 -1))) (() (Read ()) (Write ())))
|#
#|
(test-->> step
          testTerm9
          (term ((ret μ-value) defaultState)))
|#