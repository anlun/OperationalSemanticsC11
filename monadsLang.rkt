#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")

(define-extended-language lang coreLang
  ; State:
  ; AST   -- current state of program tree;
  ; η     -- current heap history;
  ; ψ (0) -- current threads read  fronts;
  ; ψ (1) -- current threads write fronts;
  ; σ     -- front after last SC operation.
  ; Invariant: ψ-read >= ψ-write
  [ξ (((AST η ψ) ψ) σ)]
  )

(define-metafunction lang
  sortξ : ξ -> ξ
  [(sortξ (((AST η ψ_read) ψ_write) σ_sc)) (((AST (sortη η) (sortψ ψ_read)) (sortψ ψ_write)) (sortσ σ_sc))])

(define preStep
  (reduction-relation
   lang #:domain ξ

   (--> (in-hole Eξ (in-hole E (in-hole EU (choice number_1 number_2))))
        (in-hole Eξ (in-hole E (in-hole EU         number_1          )))
        "num-choice-left")

   (--> (in-hole Eξ (in-hole E (in-hole EU (choice number_1 number_2))))
        (in-hole Eξ (in-hole E (in-hole EU                  number_2 )))
        "num-choice-right")
  
   (--> (in-hole Eξ (in-hole E (in-hole EU       (op number_1 number_2))))
        (in-hole Eξ (in-hole E (in-hole EU (calc (op number_1 number_2)))))
        "num-expr-calc"

        (side-condition
         (not (equal? (term op) (term choice)))))

   (--> (in-hole Eξ (in-hole E (in-hole EU           (projOp (μ_1 μ_2)))))
        (in-hole Eξ (in-hole E (in-hole EU (projCalc (projOp (μ_1 μ_2))))))
        "proj-calc")
   
   (--> (in-hole Eξ (in-hole E ((ret μ-value) >>= (λ vName AST))))
        (in-hole Eξ (in-hole E (subst vName μ-value AST)))
        ">>=-subst")

   (--> (in-hole Eξ (in-hole E (                            repeat AST))   )
        (in-hole Eξ (in-hole E (AST >>= (λ x (if x (ret x) (repeat AST))))))
        "repeat-unroll")

   (--> (in-hole Eξ (in-hole E (                            repeatFuel number     AST))   )
        (in-hole Eξ (in-hole E (AST >>= (λ x (if x (ret x) (repeatFuel number_new AST))))))
        "repeatFuel-unroll"
        (where number_new ,(- (term number) 1))

        (side-condition
         (> (term number) 0)))

   (--> (in-hole Eξ (in-hole E (repeatFuel 0 AST)))
        (((nofuel () ()) ()) ())
        "repeatFuel-nofuel")

   (--> (in-hole Eξ (in-hole E (cas SM FM ι μ-value_1 μ-value_2)))
        (((stuck () ()) ()) ())
        "cas-stuck"
        
        (side-condition
         (not (term (casMO=>? SM FM)))))
   
   (--> (in-hole Eξ (in-hole E (if 0 AST_1 AST_2)))
        (in-hole Eξ (in-hole E AST_2             ))
        "if-false")
   (--> (in-hole Eξ (in-hole E (if number AST_1 AST_2)))
        (in-hole Eξ (in-hole E AST_1                  ))
        "if-true"
        (side-condition
          (not (equal? (term number) 0))))

   ; For test results brevity only.
   (--> (in-hole Eξ (ret μ))
        ((((ret μ) () ()) ()) ())
        "heap-info-erasure"

        (side-condition     ; To eliminate cycle.
         (not (equal? (term Eξ) (term (((hole () ()) ()) ()))))))
   ))

(define-relation lang
  correctτ ⊆ τ × ι × σ
  [(correctτ τ ι σ)
   ,(not (equal? (term None) (term (lookup ι σ))))     ; This condition check if location is mentioned in front.
   ,(>= (term τ) (term (fromMaybe -1 (lookup ι σ))))
   ])

(define-relation lang
  correctE ⊆ E × Ef
  [(correctE E Ef)
   (equal? (term (pathE E)) (term (pathEf Ef)))])

(define-relation lang
  correctE2 ⊆ E × Ef × Ef
  [(correctE2 E Ef_1 Ef_2)
   ,(and
      (equal? (term (pathE E)) (term (pathEf Ef_1)))
      (equal? (term (pathE E)) (term (pathEf Ef_2))))])

(define-relation lang
  succCAScondition ⊆ ι × η × μ-value × SM × FM
  [(succCAScondition ι η μ-value SM FM)
   (nonNegativeτ (getLastTimestamp ι η))
   ,(equal? (term μ-value)
            (term (getValueByCorrectTimestamp ι (getLastTimestamp ι η) η)))
   (casMO=>? SM FM)])

(define-relation lang
  failCAScondition ⊆ ι × η × μ-value × SM × FM
  [(failCAScondition ι η μ-value SM FM)
   (nonNegativeτ (getLastTimestamp ι η))
   ,(not (equal?
          (term μ-value)
          (term (getValueByCorrectTimestamp ι (getLastTimestamp ι η) η))))
   (casMO=>? SM FM)])

(define-metafunction lang
  acqFailCASσReadNew : ι η σ -> σ
  [(acqFailCASσReadNew ι η σ_read)
   (frontMerge σ_read σ_record_front)
   
   (where τ_last         (getLastTimestamp ι η))
   (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ_last η)))])

(define-metafunction lang
  acqSuccCASσReadNew : ι η σ -> σ
  [(acqSuccCASσReadNew ι η σ_read)
   (updateFront ι τ (acqFailCASσReadNew ι η σ_read))
   (where τ (getNextTimestamp ι η))])

(define stepWOwf ; Step rules that don't use write front.
  (extend-reduction-relation
   preStep 
   lang #:domain ξ
   
   (--> (in-hole Eξ ((in-hole E (write na ι μ-value)) η (in-hole Ef σ_read)))
        (((stuck () ()) ()) ())
        "write-na-stuck"
        (side-condition (term (dontSeeLast ι η σ_read)))
        (side-condition (term (correctE E Ef))))

   (--> (in-hole Eξ ((in-hole E (read na ι)) η (in-hole Ef σ_read)))
        (((stuck () ()) ()) ())
        "read-na-stuck"
        (side-condition
         (or (term (dontSeeLast ι η σ_read))
             (term (negativeτ (getLastTimestamp ι η)))))
        (side-condition (term (correctE E Ef))))
   
   (-->        (in-hole Eξ ((in-hole E (read  rlx ι)) η (in-hole Ef σ_read    )))
        (sortξ (in-hole Eξ ((in-hole E (ret μ-value)) η (in-hole Ef σ_read_new))))
        "read-rlx"
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ_read_new                 (updateFrontAfterRead ι τ σ_read))

        (side-condition (term (correctτ τ ι σ_read)))
        (side-condition (term (correctE E Ef))))

   (-->        (in-hole Eξ ((in-hole E (read   na ι)) η (in-hole Ef σ_read)))
        (sortξ (in-hole Eξ ((in-hole E (ret μ-value)) η (in-hole Ef σ_read))))
        "read-na"
        (where τ       (getLastTimestamp ι η))
        (where μ-value (getValueByCorrectTimestamp ι τ η))
        
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (nonNegativeτ τ)))
        (side-condition (term (correctE E Ef))))

   (-->        (in-hole Eξ ((in-hole E (read  acq ι)) η (in-hole Ef σ_read    )))
        (sortξ (in-hole Eξ ((in-hole E (ret μ-value)) η (in-hole Ef σ_read_new))))
        "read-acq"
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ_read_new                 (frontMerge σ_read σ))
        
        (side-condition (term (correctτ τ ι σ_read)))
        (side-condition (term (correctE E Ef))))
   
   (--> (in-hole Eξ ((in-hole E (cas SM rlx ι μ-value_expected μ-value)) η (in-hole Ef σ_read    )))
        (in-hole Eξ ((in-hole E (ret 0                                )) η (in-hole Ef σ_read_new)))
        "cas-fail-rlx"
        (where τ          (getLastTimestamp ι η))
        (where σ_read_new (updateFrontAfterRead ι τ σ_read))

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM rlx)))
        (side-condition (term (correctE E Ef))))

   (--> (in-hole Eξ ((in-hole E (cas SM acq ι μ-value_expected μ-value)) η (in-hole Ef σ_read    )))
        (in-hole Eξ ((in-hole E (ret 0                                )) η (in-hole Ef σ_read_new)))
        "cas-fail-acq"
        (where σ_read_new (acqFailCASσReadNew ι η σ_read))

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM acq)))
        (side-condition (term (correctE E Ef))))
  ))

(define stepWOsc
  (extend-reduction-relation
   stepWOwf
   lang #:domain ξ

   (-->        (in-hole Eξ (((in-hole E (write rlx ι μ-value)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write)))
        (sortξ (in-hole Eξ (((in-hole E (ret 0))               η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write))))
        "write-rlx"
        (where τ            (getNextTimestamp ι η))
        (where σ_write_to_η (sortσ (updateFront ι τ σ_write)))
        (where η_new        (updateCell  ι μ-value σ_write_to_η η))
        (where σ_read_new   (updateFront ι τ σ_read))
        
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (-->        (in-hole Eξ (((in-hole E (write na ι μ-value)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write)))
        (sortξ (in-hole Eξ (((in-hole E (ret 0))              η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write))))
        "write-na"
        (where τ            (getNextTimestamp ι η))
        (where σ_write_to_η (sortσ (updateFront ι τ σ_write)))
        (where η_new        (updateCell  ι μ-value σ_write_to_η η))
        (where σ_read_new   (updateFront ι τ σ_read))
        
        (side-condition (term (seeLast ι η σ_read)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))
   
   (-->        (in-hole Eξ (((in-hole E (write rel ι μ-value)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write    )))
        (sortξ (in-hole Eξ (((in-hole E (ret 0))               η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write_new))))
        "write-rel"
        (where τ            (getNextTimestamp ι η))
        (where σ_read_new   (updateFront ι τ σ_read))
        (where σ_write_new  (sortσ σ_read_new))                    ; At release write we need to update write front.
        (where η_new        (updateCell  ι μ-value σ_write_new η))
        
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ (((in-hole E (cas rlx FM ι μ-value_expected μ-value_new)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write)))
        (in-hole Eξ (((in-hole E (ret 1                                    )) η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write)))
        "cas-succ-rlx"
        (where τ            (getNextTimestamp ι η))
        (where σ_read_new   (updateFront ι τ σ_read))
        (where σ_write_to_η (sortσ (updateFront ι τ σ_write)))
        (where η_new        (updateCell ι μ-value_new σ_write_to_η η))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rlx FM)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ (((in-hole E (cas rel FM ι μ-value_expected μ-value_new)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write    )))
        (in-hole Eξ (((in-hole E (ret 1                                    )) η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write_new)))
        "cas-succ-rel"
        (where τ            (getNextTimestamp ι η))
        (where σ_read_new   (updateFront ι τ σ_read))
        (where σ_write_new  (sortσ σ_read_new))
        (where η_new        (updateCell ι μ-value_new σ_write_new η))

        (side-condition
         (term (succCAScondition ι η μ-value_expected rel FM)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ (((in-hole E (cas acq FM ι μ-value_expected μ-value_new)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write)))
        (in-hole Eξ (((in-hole E (ret 1                                    )) η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write)))
        "cas-succ-acq"
        (where σ_read_new     (acqSuccCASσReadNew ι η σ_read))
        (where τ              (getNextTimestamp ι η))
        (where σ_write_to_η   (sortσ (updateFront ι τ σ_write)))
        (where η_new          (updateCell ι μ-value_new σ_write_to_η η))

        (side-condition
         (term (succCAScondition ι η μ-value_expected acq FM)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ (((in-hole E (cas relAcq FM ι μ-value_expected μ-value_new)) η     (in-hole Ef_1 σ_read    )) (in-hole Ef_2 σ_write    )))
        (in-hole Eξ (((in-hole E (ret 1                                       )) η_new (in-hole Ef_1 σ_read_new)) (in-hole Ef_2 σ_write_new)))
        "cas-succ-relAcq"
        (where σ_read_new     (acqSuccCASσReadNew ι η σ_read))
        (where σ_write_new    (sortσ σ_read_new))
        (where η_new          (updateCell ι μ-value_new σ_write_new η))

        (side-condition
         (term (succCAScondition ι η μ-value_expected relAcq FM)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ (((in-hole E (spw AST_1 AST_2)) η (in-hole Ef_1             σ_read))  (in-hole Ef_2              σ_write)))
        (in-hole Eξ (((in-hole E (par AST_1 AST_2)) η (in-hole Ef_1 (par σ_read σ_read))) (in-hole Ef_2 (par σ_write σ_write))))
        "front-dup"
        (side-condition (term (correctE2 E Ef_1 Ef_2))))
   
   (-->        (in-hole Eξ (((in-hole E (par (ret μ-value_1) (ret μ-value_2))) η (in-hole Ef_1 (par        σ_read1 σ_read2))) (in-hole Ef_2 (par        σ_write1 σ_write2))))
        (sortξ (in-hole Eξ (((in-hole E (ret (μ-value_1           μ-value_2))) η (in-hole Ef_1 (frontMerge σ_read1 σ_read2))) (in-hole Ef_1 (frontMerge σ_write1 σ_write2)))))
        "par-join"
        (side-condition (term (correctE2 E Ef_1 Ef_2))))
   ))

(define step
  (extend-reduction-relation
   stepWOsc
   lang #:domain ξ

   (-->        (in-hole Eξ ((((in-hole E (write sc ι μ-value)) η     (in-hole Ef_1 σ_read)) (in-hole Ef_2 σ_write)) σ_sc ))
        (sortξ (in-hole Eξ ((((in-hole E (ret 0))              η_new (in-hole Ef_1 σ_new )) (in-hole Ef_2 σ_new  )) σ_new)))
        "write-sc"
        (where τ          (getNextTimestamp ι η))
        (where σ_with_sc  (frontMerge σ_read σ_sc))
        (where σ_new      (updateFront ι τ σ_with_sc))
        (where η_new      (updateCell  ι μ-value (sortσ σ_new) η))
        
        (side-condition (term (correctE2 E Ef_1 Ef_2))))
      
   (-->        (in-hole Eξ ((((in-hole E (read   sc ι)) η (in-hole Ef_1 σ_read)) (in-hole Ef_2 σ_write)) σ_sc ))
        (sortξ (in-hole Eξ ((((in-hole E (ret μ-value)) η (in-hole Ef_1 σ_new )) (in-hole Ef_2 σ_new  )) σ_new)))
        "read-sc"
        (where (in-hole El (τ μ-value σ)) (getCellHistory ι η))
        (where σ_with_sc                  (frontMerge σ_read σ_sc))
        (where σ_new                      (frontMerge σ_with_sc σ))
        
        (side-condition (term (correctτ τ ι σ_with_sc)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ ((((in-hole E (cas SM sc ι μ-value_expected μ-value)) η (in-hole Ef_1 σ_read)) (in-hole Ef_2 σ_write)) σ_sc ))
        (in-hole Eξ ((((in-hole E (ret 0                               )) η (in-hole Ef_1 σ_new )) (in-hole Ef_2 σ_new  )) σ_new))
        "cas-fail-sc"
        (where τ              (getLastTimestamp ι η))
        (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ η)))
        (where σ_read_sync    (frontMerge σ_read σ_record_front))
        (where σ_new          (frontMerge σ_read_sync σ_sc))

        (side-condition
         (term (failCAScondition ι η μ-value_expected SM sc)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))

   (--> (in-hole Eξ ((((in-hole E (cas sc FM ι μ-value_expected μ-value_new)) η     (in-hole Ef_1 σ_read)) (in-hole Ef_2 σ_write)) σ_sc ))
        (in-hole Eξ ((((in-hole E (ret 1                                   )) η_new (in-hole Ef_1 σ_new )) (in-hole Ef_2 σ_new  )) σ_new))
        "cas-succ-sc"
        (where τ              (getNextTimestamp ι η))
        (where τ_last         (getLastTimestamp ι η))
        (where σ_record_front (fromMaybe () (getFrontByTimestamp ι τ_last η)))
        (where σ_with_sc      (frontMerge σ_sc σ_record_front))
        (where σ_read_new     (updateFront ι τ (frontMerge σ_read σ_with_sc)))
        (where σ_new          (sortσ σ_read_new))
        (where η_new          (updateCell ι μ-value_new σ_new η))

        (side-condition
         (term (succCAScondition ι η μ-value_expected sc FM)))
        (side-condition (term (correctE2 E Ef_1 Ef_2))))
))

;;;;;;;;;;;;;;;;;
; Tests
;;;;;;;;;;;;;;;;;
(define testTerm-1
         (term (((((spw (ret (+ 1 2)) (ret (+ 3 9))) >>= (λ v
                   (ret v)))
                   () ()) ()) ())))

(test-->> step
          testTerm-1
          (term ((((ret (3 12)) () ()) ()) ())))

#|
y_rlx  = 1 || x_rlx = 1
R1 = x_rlx || R2 = y_rlx

Can lead to R1 = R2 = 0.
|#
(define testTerm0
          (term (((((spw
                   ((write rlx "y" 1) >>= (λ x (
                    (read  rlx "x")   >>= (λ x
                    (ret x)))))
                   ((write rlx "x" 1) >>= (λ x (
                    (read  rlx "y")   >>= (λ x
                    (ret x))))))
                  >>=
                  (λ x (ret x)))

                  (("x" ((0 0 (("x" 0))))) ("y" ((0 0 (("y" 0))))))
                  (("x" 0) ("y" 0)))
                  (("x" 0) ("y" 0)))
                  () )))

(test-->>∃ step
          testTerm0
          (term ((((ret (0 0)) () ()) ()) ())))

#|
y_rel  = 1 || x_rel = 1
R1 = x_acq || R2 = y_acq

Can lead to R1 = R2 = 0.
|#
(define testTerm1
        (term (((((spw
                   ((write rel "y" 1) >>= (λ x (
                    (read  acq "x")   >>= (λ x
                    (ret x)))))
                   ((write rel "x" 1) >>= (λ x (
                    (read  acq "y")   >>= (λ x
                    (ret x))))))
                  >>=
                  (λ x (ret x)))
                 
                  (("x" ((0 0 (("x" 0))))) ("y" ((0 0 (("y" 0))))))
                  (("x" 0) ("y" 0)))
                  (("x" 0) ("y" 0)))
                  () )))

(test-->>∃ step
          testTerm1
          (term ((((ret (0 0)) () ()) ()) ())))

#|
x_na = 1 || x_na = 2

It should get `stuck`.
|#
(define testTerm2
        (term (((((spw
                   ((write na "x" 1) >>= (λ x (ret 1)))
                   ((write na "x" 2) >>= (λ x (ret 2))))
                  >>=
                  (λ x (ret x)))
                  () ()) ()) ())))

(test-->>∃ step
          testTerm2
          (term (((stuck () ()) ()) ())))

#|
       c_rlx = 0;
a_na  = 7; || repeat (c_acq) end;
c_rel = 1  || a_na = a_na + 1
       ret a_na

Example from: VafeiadisNarayan:OOPSLA13 "Relaxed Separation Logic: A Program Logic for C11 Concurrency".

It shouldn't get `stuck`.
|#
(define testTerm3
         (term ((((((write rlx "c" 0) >>= (λ x
                    (spw
                     ((write na  "a" 7) >>= (λ x
                      (write rel "c" 1)))
                     ((repeat (read acq "c")) >>= (λ x
                     ((read  na "a") >>= (λ x
                      (write na "a" (+ 1 x))))
                      ))
                    )))
                    >>= (λ x (read na "a")))
                    () ()) ()) ())))

;(test-->> step
;         testTerm3
;         (term (((stuck () ()) ()) ())))

(define value? (redex-match lang (ret μ-value)))
#|
(test-->> step
         testTerm3
         value?)
|#

#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rlx = 0;
               y_rlx = 0;
x_rel = 1;         || y_rel = 1;
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(define testTerm4
         (term (((((write rlx "x" 0) >>= (λ x
                  ((write rlx "y" 0) >>= (λ x
                   (spw
                    ((write rel "x" 1) >>= (λ x
                    ((read  acq "y"  ) >>= (λ y
                     (if (== 0 y) (write na "a" 239) (ret 0))))))
                    ((write rel "y" 1) >>= (λ x
                    ((read  acq "x"  ) >>= (λ x
                     (if (== 0 x) (write na "a" 30 ) (ret 0))))))
                    )
                    )) ))
                  () ()) ()) ())))

(test-->>∃ step
           testTerm4
           (term (((stuck () ()) ()) ())))

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

#|
                     x_rlx = 0
x_rlx = 1 || x_rlx = 2 || a = x_rlx || c = x_rlx
          ||           || b = x_rlx || d = x_rlx

The execution a = d = 1 and b = c = 2 is invalid.
Again I don't know how to say 'this can't be reduced to that' in tests, so this test should fail.
|#
(define testTerm6
        (term (((((write rlx "x" 0) >>= (λ x
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
                 (ret (proj2 x))))))
                () ()) ()) ())))
#|
(test-->>∃ step
          testTerm6
          (term ((((ret (1 2) (2 1)) () ()) ()) ())))
|#

#|
IRIW. Anti-TSO example.

                     x_rlx = 0
                     y_rlx = 0
x_rlx = 1 || y_rlx = 1 || a = x_rlx || c = y_rlx
          ||           || b = y_rlx || d = x_rlx

The test takes too many time to execute. Results are:

  actual: '((ret ((0 0) (0 0))) () (() ()) ())
  actual: '((ret ((0 0) (0 1))) () (() ()) ())
  actual: '((ret ((0 0) (1 0))) () (() ()) ())
  actual: '((ret ((0 0) (1 1))) () (() ()) ())
  actual: '((ret ((0 1) (0 0))) () (() ()) ())
  actual: '((ret ((0 1) (0 1))) () (() ()) ())
  actual: '((ret ((0 1) (1 0))) () (() ()) ())
  actual: '((ret ((0 1) (1 1))) () (() ()) ())
  actual: '((ret ((1 0) (0 0))) () (() ()) ())
  actual: '((ret ((1 0) (0 1))) () (() ()) ())
  actual: '((ret ((1 0) (1 0))) () (() ()) ())
  actual: '((ret ((1 0) (1 1))) () (() ()) ())
  actual: '((ret ((1 1) (0 0))) () (() ()) ())
  actual: '((ret ((1 1) (0 1))) () (() ()) ())
  actual: '((ret ((1 1) (1 0))) () (() ()) ())
  actual: '((ret ((1 1) (1 1))) () (() ()) ())

The `ret ((1 0) (0 1))` shows that our model is more relaxed than x86-TSO [Sewell-al:CACM10].
|#
(define testTerm65
        (term (((((write rlx "x" 0) >>= (λ x
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
                 (ret (proj2 x))))))))
                () ()) ()) ())))
#|
(test-->> step
          testTerm65
          (term ((((ret (1 0) (1 0)) () ()) ()) ())))
|#

#|
Anti-TSO example.
It shows why our model isn't TSO.

      x = 0; y = 0
x_rlx = 1; || a = y_rlx;
y_rlx = 1  || b = x_rlx

In TSO a = 1 and b = 0 is forbidden outcome. But not in our semantics.
|#

(define testTerm7
  (term (((((write rlx "x" 0) >>= (λ x
           ((write rlx "y" 0) >>= (λ x
           ((spw
            ((write rlx "x" 1) >>= (λ x
             (write rlx "y" 1)))
            ((read rlx "y") >>= (λ a
            ((read rlx "x") >>= (λ b
             (ret (a b))))))
            ) >>= (λ x
            (ret (proj2 x))))))))
           () ()) ()) ())))

(test-->>∃ step
           testTerm7
           (term ((((ret (1 0)) () ()) ()) ())))


#|
cas rlx sc "x" 1 0

Leads to `stuck` state, because Compare-and-Set (Read-Modify-Write) operations in C11 are
undefined if success modifier is weaker than fail modifier.
|#
(define testTerm8
  (term ((((cas rlx sc "x" 1 0) () ()) ()) ())))

(test-->> step
          testTerm8
          (term (((stuck () ()) ()) ())))


#|
An example from VafeiadisNarayan:OOPSLA13. It shouldn't get `stuck`.

                    lock = 1
a_na     = 2 || if (cas_acq_rlx lock 0 1) then || if (cas_acq_rlx lock 0 1)
lock_rel = 0 ||    a_na = 3                    ||    a_na = 2
                    ret a
|#

(define testTerm9
  (term (((((write rlx "lock" 1) >>= (λ x
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
            () ()) ()) ())))

#|
  actual: '((ret (0 (-1 -1))) () (() ()) ())
  actual: '((ret (0 (-1 0))) () (() ()) ())
  actual: '((ret (0 (0 -1))) () (() ()) ())

(test-->> step
          testTerm9
          value?)
|#

(define term0
  (term (((((spw
             (ret (+ 1 2))
             (ret (+ 3 9)))
            >>=
            (λ v (ret v))) () ()) ()) ())))
;(traces step term1)