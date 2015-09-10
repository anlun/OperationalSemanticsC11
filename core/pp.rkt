#lang racket
(require redex)
(require racket-pretty-printing-combinators)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "../tests/testTerms.rkt")
(provide pretty-printer)

(current-page-width 150)
(define tabstop (make-parameter 3))

(define-metafunction coreLang
  ; ppExpr : Expr -> Doc
  [(ppExpr vName ) ,(symbol->string (term vName ))]
  [(ppExpr number) ,(number->string (term number))]
  [(ppExpr (op Expr_0 Expr_1))
   ,(beside* "(" (symbol->string (term op))
             (term (ppExpr Expr_0))
             " "
             (term (ppExpr Expr_1))
             ")")])

(define-metafunction coreLang
  ; ppμ : μ -> Doc
  [(ppμ ι-var) (ppι-var ι-var)]
  [(ppμ (μ_0 μ_1))
   ,(beside*
     "(" (term (ppμ μ_0)) " " (term (ppμ μ_1)) ")")]
  [(ppμ Expr) (ppExpr Expr)]
  [(ppμ (proj1 μ))
   ,(beside (term (ppμ μ)) "_1")]
  [(ppμ (proj2 μ))
   ,(beside (term (ppμ μ)) "_2")])

(define-metafunction coreLang
  isUsed : vName AST -> boolean
  [(isUsed vName AST) #f
                      (side-condition (equal? (term (subst vName 1 AST)) (term AST)))]
  [(isUsed vName AST) #t])

(define-metafunction coreLang
  ; ppWM : WM -> Doc
  [(ppWM rlx) "rlx"]
  [(ppWM rel) "rel"]
  [(ppWM sc ) "sc "]
  [(ppWM na ) "na "])

(define-metafunction coreLang
  ; ppRM : RM -> Doc
  [(ppRM rlx) "rlx"]
  [(ppRM acq) "acq"]
  [(ppRM sc ) "sc" ]
  [(ppRM na ) "na" ])

(define-metafunction coreLang
  ppι-var : ι-var -> string
  [(ppι-var ι) ι]
  [(ppι-var vName) ,(symbol->string (term vName))])

(define-metafunction coreLang
  ;pp : AST -> Doc
  
  [(pp (AST_0 >>= (λ vName AST_1)))
   ,(above
     (beside*
       (symbol->string (term vName))
       " := " (term (pp AST_0)) ";")
     (term (pp AST_1)))
   (side-condition (term (isUsed vName AST_1)))]
  [(pp (AST_0 >>= (λ vName AST_1)))
   ,(above
     (beside (term (pp AST_0)) ";")
     (term (pp AST_1)))
   (side-condition (not (term (isUsed vName AST_1))))]
  
  [(pp (write WM ι-var μ))
   ,(beside*
     (term (ppι-var ι-var)) "_"
     (term (ppWM WM))       " := "
     (term (ppμ μ)))]
  
  [(pp (read RM ι-var))
   ,(beside* (term (ppι-var ι-var)) "_"
             (term (ppRM RM)))]
  
  [(pp (spw AST_0 AST_1))
   ,(above*
     "spw"
     (beside "{{{ " (term (pp AST_0)))
     "\\\\\\"
     (indent (string-length "{{{ ")
             (beside (term (pp AST_1))" }}}")))]
  
  [(pp (spw AST_0 AST_1))
   ,(above*
     "par"
     (beside "{{{ " (term (pp AST_0)))
     "\\\\\\"
     (indent (string-length "{{{ ")
             (beside (term (pp AST_1))" }}}")))]
  
  [(pp (ret μ)) ,(beside
                  "return "
                  (term (ppμ μ)))]
  [(pp AST) "___"])

(define pretty-printer
  (λ (t port w txt)
    (write-string (doc->string (term (pp ,(list-ref t 0)))) port)))

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