#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "../tests/testTerms.rkt")

(define-metafunction coreLang
  ppμ : μ -> string
  [(ppμ ι-var) (ppι-var ι-var)]
  [(ppμ (μ_0 μ_1))
   ,(string-append
     "("
     (term (ppμ μ_0))
     " "
     (term (ppμ μ_1))
     ")")]
  [(ppμ μ) "___"])

(define-metafunction coreLang
  isUsed : vName AST -> boolean
  [(isUsed vName AST) #f
                      (side-condition (equal? (term (subst vName 1 AST)) (term AST)))]
  [(isUsed vName AST) #t])

(define-metafunction coreLang
  ppWM : WM -> string
  [(ppWM rlx) "rlx"]
  [(ppWM rel) "rel"]
  [(ppWM sc ) "sc "]
  [(ppWM na ) "na "])

(define-metafunction coreLang
  ppι-var : ι-var -> string
  [(ppι-var ι) ι]
  [(ppι-var vName) ,(symbol->string (term vName))])

(define-metafunction coreLang
  pp : AST -> string
  
  [(pp (AST_0 >>= (λ vName AST_1)))
   ,(string-append
     (symbol->string (term vName))
     " := "
     (term (pp AST_0))
     ";\n"
     (term (pp AST_1)))
   (side-condition (term (isUsed vName AST_1)))]
  [(pp (AST_0 >>= (λ vName AST_1)))
   ,(string-append
     (term (pp AST_0))
     ";\n"
     (term (pp AST_1)))
   (side-condition (not (term (isUsed vName AST_1))))]
  
  [(pp (write WM ι-var μ))
   ,(string-append
     (term (ppι-var ι-var))
     "_"
     (term (ppWM WM))
     " := "
     (term (ppμ μ)))]
  
  [(pp (spw AST_0 AST_1))
   ,(string-append
     "spw\n"
     (term (pp AST_0))
     "\n"
     (term (pp AST_1)))]
  
  [(pp (ret μ)) ,(string-append
                  "return "
                  (term (ppμ μ)))]
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