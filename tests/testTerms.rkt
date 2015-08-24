#lang racket
(require redex)
(provide (all-defined-out))

#|
y_rlx  = 1 || x_rlx  = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(define testTerm0 (term
                  ((write rlx "x" 0) >>= (λ z
                  ((write rlx "y" 0) >>= (λ z
                  ((spw
                   ((write rlx "y" 1) >>= (λ z
                   ((read  rlx "x")   >>= (λ x
                    (ret x)))))
                   ((write rlx "x" 1) >>= (λ z
                   ((read  rlx "y")   >>= (λ y
                    (ret y))))))
                  >>=
                  (λ z (ret z)))))))))

#|
R1 = x_rlx || R2 = y_rlx
y_rlx  = 1 || x_rlx  = 1

With postponed reads it should be able to lead to R1 = R2 = 1.
|#
(define testTerm01 (term
                  ((write rlx "x" 0) >>= (λ z
                  ((write rlx "y" 0) >>= (λ z
                  ((spw
                   ((read  rlx "x")   >>= (λ x
                   ((write rlx "y" 1) >>= (λ z
                    (ret x)))))
                   ((read  rlx "y")   >>= (λ y
                   ((write rlx "x" 1) >>= (λ z
                    (ret y))))))
                  >>=
                  (λ x (ret x)))))))))

#|
R1 = x_rlx || R2 = y_rlx
y_sc   = 1 || x_sc   = 1

With postponed reads it shouldn't be able to lead to R1 = R2 = 1, because of sc operations.
|#
(define testTerm02 (term
                  ((write rlx "x" 0) >>= (λ z
                  ((write rlx "y" 0) >>= (λ z
                  ((spw
                   ((read  rlx "x")   >>= (λ x
                   ((write sc  "y" 1) >>= (λ z
                    (ret x)))))
                   ((read  rlx "y")   >>= (λ y
                   ((write sc  "x" 1) >>= (λ z
                    (ret y))))))
                  >>=
                  (λ x (ret x)))))))))

#|
R1 = x_rlx || R2 = y_rlx
y_rel  = 1 || x_rel  = 1

With postponed reads it shouldn't be able to lead to R1 = R2 = 1, because of rel operations.
|#
(define testTerm03 (term
                  ((write rlx "x" 0) >>= (λ z
                  ((write rlx "y" 0) >>= (λ z
                  ((spw
                   ((read  rlx "x")   >>= (λ x
                   ((write rel "y" 1) >>= (λ z
                    (ret x)))))
                   ((read  rlx "y")   >>= (λ y
                   ((write rel "x" 1) >>= (λ z
                    (ret y))))))
                  >>=
                  (λ x (ret x)))))))))


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

The `ret ((1 0) (0 1))` shows that our model is more relaxed than x86-TSO [Sewell-al:CACM10].
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
x_rlx = 1; || a = y_rlx;
y_rlx = 1  || b = x_rlx

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
