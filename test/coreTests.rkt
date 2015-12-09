#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")
(require "../core/parser.rkt")

;;;;;;;;;;;;;;;;;
; syntax
;;;;;;;;;;;;;;;;;
(define (metafunction-tests)
  (test-equal (pair<? '("x" 1) '("y" 0))
              #t)

  (test-equal (term (sortσ (("x" 1) ("z" 30) ("y" 2) ("ab" 239))))
              '(("ab" 239) ("x" 1) ("y" 2) ("z" 30)))

  (test-equal (term (lookup "x" (("y" 1) ("z" 2))))
              (term None))
  (test-equal (term (lookup "x" (("y" 1) ("x" 2))))
              (term (Just 2)))
  
  (test-equal (term (removeByKey "x" (("y" 1) ("x" 2))))
              (term (("y" 1))))
  
  (test-equal (term (maxLookup "x" 1 (("y" 1) ("x" 2))))
              (term ("x" 2)))
  
  (test-equal (term (frontMerge (("y" 1) ("x" 2)) (("z" 3) ("x" 1))))
              (term (("x" 2) ("y" 1) ("z" 3))))
  (test-equal (term (frontMerge (("y" 1) ("x" 1)) (("z" 3) ("x" 2))))
              (term (("x" 2) ("y" 1) ("z" 3))))
  
  (test-equal (term (getCellHistory "x"
                                    (("y" ((3 2 ()) (1 1 ()) (0 2 ()))) ("x" ((3 3 ()) (2 2 ()) (1 1 ()))))))
              (term ((3 3 ()) (2 2 ()) (1 1 ()))))
  (test-equal (term (getNextTimestampFromCellHistory ((3 3 ()) (2 2 ()) (1 1 ()))))
              (term 4))
  
  (test-equal (term (updateCell "x" 239 ()
                                (("y" ((3 2 ()) (1 1 ()) (0 2 ()))) ("x" ((3 3 ()) (2 2 ()) (1 1 ()))))))
              (term (("x" ((4 239 ()) (3 3 ()) (2 2 ()) (1 1 ()))) ("y" ((3 2 ()) (1 1 ()) (0 2 ()))))))

  (test-equal (term (subst b x (read rlx b)))
              (term (read rlx x)))

  (test-equal (term (substι b x b))
              (term x))
  
  (test-results))
(metafunction-tests)

;;;;;;;;;;;;;;;;;
; coreLang
;;;;;;;;;;;;;;;;;
(define-term defaultState (()))
(define-metafunction coreLang
  spwST : path auxξ -> auxξ
  [(spwST path auxξ) auxξ])
(define-metafunction coreLang
  joinST : path auxξ -> auxξ
  [(joinST path auxξ) auxξ])

(define step (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t))
(define test (define-coreTest step defaultState))

;;;;;;;;;;;;;;;;;
; coreUtils
;;;;;;;;;;;;;;;;;
(define (coreUtils-tests)
  (test-equal
   (getLastNodeNumber_gr (term (((1 skip)) ())))
   1)
  (test-equal
   (getLastNodeNumber_gr
    (term (((1 skip) (4 (read rlx x 10)) (5 (write rlx y 34))) ())))
   5)
  
  (test-equal
   (term (spwST_gr () (() (Graph (((0 skip)) ())) (GFront 0))))
   (term (() (Graph (((1 skip) (0 skip)) ((0 1 sb)))) (GFront (par 1 1)))))

  (test-equal
   (term (are∀PostReadsRlx () (() (P ((x "x" rlx))))))
   #t)

  (test-equal
   (term (are∀PostReadsRlx () (() (P ((x "x" acq) (y "y" rlx))))))
   #f)

  (test-equal
   (term (are∀PostReadsRlx () (())))
  #t))
(coreUtils-tests)

;;;;;;;;;;;;;;;;;
; graphUtils
;;;;;;;;;;;;;;;;;
(define-term nodes0
  ((0 (write rel "x" 1 0))
   (1 skip)
   (2 (write rel "x" 2 1))
   (3 (write rlx "x" 3 2))
   (4 (read  acq "x" 3))))

(define-term edges0
  ((0 1 sb)
   (1 2 sb)
   (1 4 sb)
   (2 3 sb)
   (3 4 rf)))

(define-term testGraph0
  (nodes0 edges0))

(define-term testGraph0_with_sw
  (nodes0 ,(cons (term (2 4 sw)) (term edges0))))

(define-term testGraph1
  (((0 (write rel "x" 1 0))
    (1 skip)
    (2 (write rlx "x" 2 1))
    (3 (read  acq "x" 2)))
   ((0 1 sb)
    (1 2 sb)
    (1 3 sb)
    (2 3 rf))))

(define (graphUtils-tests)
  (test-equal (term (addSWedges 4 testGraph0)) (term testGraph0_with_sw))
  (test-equal (term (addSWedges 3 testGraph1)) (term testGraph1))
  (test-equal (prevNodesOnThread_num 3 (term edges0) (term nodes0)) (term (2))))
(graphUtils-tests)

;;;;;;;;;;;;;;;;;
; Parser
;;;;;;;;;;;;;;;;;
(define (parser-tests)
  (test-equal (parse "ret 3 - 3 * 6")
              '(ret (- 3 (* 3 6))))
  (test-equal (parse "ret 3 + 3 * 6 == 21")
              '(ret (== (+ 3 (* 3 6)) 21)))
  (test-equal (parse "ret [3 3]_2")
              '(ret (proj2 (3 3))))
  (test-equal (parse "ret [r1 6]")
              '(ret (r1 6)))
  (test-equal (parse "ret [x 6]")
              '(ret ("x" 6)))
  (test-equal (parse "x_rel := 5")
              '(write rel "x" 5))
  (test-equal (parse "x_acq")
              '(read acq "x"))
  (test-equal (parse "cas_rel_rlx(x, 1, 2)")
              '(cas rel rlx "x" 1 2))
  (test-equal (parse "if r1 then ret 1 else ret 2")
              '(if r1 (ret 1) (ret 2)))
  (test-equal (parse "repeat x_acq end")
              '(repeat (read acq "x")))
  (test-equal (parse "r1 := ret 2; ret 3")
              '((ret 2) >>= (λ r1 (ret 3))))
  (test-equal (parse "spw {{{ ret 2 \\\\\\ ret 3 }}}")
              '(spw (ret 2) (ret 3)))
  (test-equal (parse "stuck")
              'stuck)
  (test-equal (parse "ret choice 3 (3 + 6)")
              '(ret (choice 3 (+ 3 6)))))
(parser-tests)
