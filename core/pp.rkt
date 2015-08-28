#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "../tests/testTerms.rkt")

(define-metafunction coreLang
  pp : AST -> string
  [(pp (AST_0 >>= (λ vName AST_1)))
   ,(string-append
     ; (term vName)
     ":= "
     (term (pp AST_0))
     ";\n"
     (term (pp AST_1)))]
  [(pp AST) "___"])

(define pretty-printer
  (λ (t port w txt)
    (write-string (term (pp ,(list-ref t 0))) port)))

(define-term defaultState (()))
(define-metafunction coreLang
  spwST : path auxξ -> auxξ
  [(spwST path auxξ) auxξ])
(define-metafunction coreLang
  joinST : path auxξ -> auxξ
  [(joinST path auxξ) auxξ])

(define step (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t))
(traces step (term (,testTerm01 defaultState))
        #:pp pretty-printer)