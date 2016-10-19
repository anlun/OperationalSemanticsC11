#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")
(require "../core/parser.rkt")
(require "../core/pp.rkt")
(require "../test/testTerms.rkt")

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
  
  (test-equal (term (getσToWrite (("a" 1) ("x" 1))
                                 "x"
                                 (("a"
                                   ((1 5 (("a" 1)))
                                    (0 0 (("a" 0)))))
                                  ("x"
                                   ((1 1 (("a" 1) ("x" 1)))
                                    (0 0 (("x" 0))))))))
              (term (("a" 1) ("x" 1))))

  (test-equal (term (canPostponedWriteBePerformed (a3 "y")
                                                  ((read  a1 "x"  rlx ())
                                                   (write a2 "z1" rlx a1)
                                                   (write a3 "y"  rlx 1))))
              (term #t))
  (test-equal (term (canPostponedReadBePerformed (a "x" rlx ())
                                                 (("x" 0) ("y" 1))
                                                 ((read a "x" rlx ())) () () 0))
              (term #t))

  (test-equal (term (isPEntryInConflictWithEifα (read a2 "dataP") ((if a1 1 hole ()))))
              (term #f))
  
  (test-equal (term (resolveWriteγ_η_el a (("a" 1)) ("x" 1 a) 
                     (("a" ((1 1 (("a" 1))) (0 0 (("a" 0)))))
                      ("x" ((2 3 (("a" 0) ("x" 2)))
                            (1 1 (("a" 0) ("x" 1)))
                            (0 0 (("x" 0))))))))

              (term (("a" ((1 1 (("a" 1))) (0 0 (("a" 0)))))
                     ("x" ((2 3 (("a" 0) ("x" 2)))
                           (1 1 (("a" 1) ("x" 1)))
                           (0 0 (("x" 0))))))))
)
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

(define step (define-coreStep defaultState spwST joinST))
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
   (term (spwST-gr () (() (Graph (((0 skip)) ())) (GFront 0))))
   (term (() (Graph (((1 skip) (0 skip)) ((0 1 sb)))) (GFront (par 1 1)))))

  (test-equal
   (term (are∀PostReadsRlx () (() (P ((read x "x" rlx ()))))))
   #t)

  (test-equal
   (term (are∀PostReadsRlx () (() (P ((read x "x" acq ()) (read y "y" rlx ()))))))
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
  (test-equal @prog{ret 3 - 3 * 6}
              '(ret (- 3 (* 3 6))))

  (test-equal @prog{ret 3 + 3 * 6 == 21}
              '(ret (== (+ 3 (* 3 6)) 21)))

  (test-equal @prog{ret 3 + 3 * 6 <= 21}
              '(ret (<= (+ 3 (* 3 6)) 21)))

  (test-equal @prog{ret [3 3]_2}
              '(ret (proj2 (3 3))))

  (test-equal @prog{ret [r1 6]}
              '(ret (r1 6)))

  (test-equal @prog{ret [x 6]}
              '(ret ("x" 6)))

  (test-equal @prog{x_rel := 5}
              '(write rel "x" 5))

  (test-equal @prog{x_acq}
              '(read acq "x"))

  (test-equal @prog{cas_rel_rlx(x, 1, 2)}
              '(cas rel rlx "x" 1 2))

  (test-equal @prog{if r1
                    then ret 1
                    else ret 2
                    fi}
              '(if r1 (ret 1) (ret 2)))

  (test-equal @prog{repeat x_acq end}
              '(repeat (read acq "x")))

  (test-equal @prog{r1 := ret 2;
                    ret 3}
              '((ret 2) >>= (λ r1 (ret 3))))

  (test-equal @prog{spw {{{ ret 2
                        ||| ret 3 }}} }
              '(spw (ret 2) (ret 3)))

  (test-equal @prog{stuck}
              'stuck)

  (test-equal @prog{ret choice 3 (3 + 6)}
              '(ret (choice 3 (+ 3 6))))

  (test-equal @prog{ret 3;
                    ret 4}
              '((ret 3) >>= (λ r-1 (ret 4))))

  (test-equal @prog{x_rlx := 0;
                    y_rlx := 0}
              '((write rlx "x" 0) >>= (λ r-1
                (write rlx "y" 0))))

  (test-equal @prog{x_rlx := 0;
                    y_rlx := 0;
                    ra := ret 5;
                    ret ra}
              '((write rlx "x" 0) >>= (λ r-1
               ((write rlx "y" 0) >>= (λ r-1
               ((ret 5) >>= (λ ra
                (ret ra))))))))

  (test-equal @prog{x_rlx := 0;
                    y_rlx := 0;
                    ra := spw
                          {{{ ret 3
                          |||
                              ret 5 }}};
                    ret ra}
              '((write rlx "x" 0) >>= (λ r-1
               ((write rlx "y" 0) >>= (λ r-1
               ((spw (ret 3) (ret 5)) >>= (λ ra
                (ret ra))))))))

  (test-equal @prog{r1 := if 0
                          then ret 0
                          else ret 0
                          fi;
                    ret r1}
              '((if 0 (ret 0) (ret 0)) >>= (λ r1
                (ret r1))))

  (test-equal @prog{fence sc}
              '(fence sc)))
(parser-tests)

(define (pp-parser-test term)
  (test-equal (parse (ast-print term))
              term))

(define (pp-parser-tests)
  (pp-parser-test testTerm-1)
  (pp-parser-test term_WrlxRrlx_WrlxRrlx))
