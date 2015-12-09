#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../core/graphUtils.rkt")

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
(let ((input (open-input-string "ret 3 - 3 * 6")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "ret 3 + 3 * 6 == 21")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "ret [3 3]_2")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "ret [r1 6]")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "ret [x 6]")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "x_rel := 5")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "x_acq")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "cas_rel_rlx(x, 1, 2)")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "if r1 then ret 1 else ret 2")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "repeat x_acq end")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "r1 := ret 2; ret 3")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "spw {{{ ret 2 \\\\\\ ret 3 }}}")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "stuck")))
  (lang-parser (lex-this lang-lexer input)))

(let ((input (open-input-string "ret choice 3 (3 + 6)")))
  (lang-parser (lex-this lang-lexer input)))
