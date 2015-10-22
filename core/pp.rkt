#lang racket ;/gui
(require redex/reduction-semantics)
(require racket-pretty-printing-combinators)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(require "../tests/testTerms.rkt")
(provide pretty-printer)

(current-page-width 1050)
(define tabstop (make-parameter 3))
(define state-width (make-parameter 50))

(define (above** xs)
  (foldr above (empty-doc) xs))

(define-metafunction coreLang
  ; ppExpr : Expr -> Doc
  [(ppExpr vName ) ,(symbol->string (term vName ))]
  [(ppExpr number) ,(number->string (term number))]
  [(ppExpr (op Expr_0 Expr_1))
   ,(beside* "(" (symbol->string (term op)) " "
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
  ; ppMod : WM/RM/SM/FM -> Doc
  [(ppMod rlx   ) "rlx"]
  [(ppMod acq   ) "acq"]
  [(ppMod rel   ) "rel"]
  [(ppMod sc    ) "sc" ]
  [(ppMod relAcq) "relAcq"]
  [(ppMod na    ) "na" ])

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
     (term (ppMod WM))      " := "
     (term (ppμ μ)))]
  
  [(pp (read RM ι-var))
   ,(beside* (term (ppι-var ι-var)) "_"
             (term (ppMod RM)))]
  
  [(pp (cas SM FM ι-var μ_0 μ_1))
   (beside*
    (beside* "cas_" (term (ppMod SM)) "_" (term (ppMod FM)) "(")
    (term (ppι-var ι-var)) ", "
    (term (ppμ μ_0)) ", "
    (term (ppμ μ_1)))]
  
  [(pp (spw AST_0 AST_1))
   ,(pp-par "spw" (term (pp AST_0))
                  (term (pp AST_1)))]
  
  [(pp (par AST_0 AST_1))
   ,(pp-par "par" (term (pp AST_0))
                  (term (pp AST_1)))]
  
  [(pp (if Expr AST_0 AST_1))
   ,(above* (beside "if "   (term (ppExpr Expr)))
            (beside "then " (term (pp AST_0)))
            (beside "else " (term (pp AST_1))))]
  
  [(pp (repeat AST))
   ,(beside* "repeat " (term (pp AST)) " end")]

  [(pp (repeatFuel number AST))
   ,(beside* "repeatFuel " (number->string (term number))
             " " (term (pp AST)) " end")]  
  
  [(pp (ret μ)) ,(beside
                  "return "
                  (term (ppμ μ)))]
  [(pp AST) ,(~a (term AST))])

(define-metafunction coreLang
  ; ppη-cell : η-cell -> Doc
  [(ppη-cell η-cell)
   ,(above**
     (map (λ (h)
            (match h
              [(list n_0 n_1 s)
               (beside*/space "τ:" (number->string n_0)
                              "μ:" (number->string n_1)
                              (term (ppσ ,s)))]))
          (term η-cell)))])

(define-metafunction coreLang
  ; ppι-η-cell : (ι η-cell) -> Doc
  [(ppι-η-cell (ι η-cell))
   ,(beside*/space (term ι) "↦"
                   (term (ppη-cell η-cell)))])

(define-metafunction coreLang
  ; ppσ : σ -> Doc
  [(ppσ σ) ,(above** (map
                      (λ (h)
                        (match h
                          [(list l v)
                           (beside* "(" l " τ≥ " (number->string v) ")")]))
                      (term σ)))])

(define-metafunction coreLang
  ; ppη : η -> Doc
  [(ppη η) ,(above** (map
                      (λ (h) (term (ppι-η-cell ,h)))
                      (term η)))])
(define-metafunction coreLang
  ; ppψ : ψ -> Doc
  [(ppψ σ) (ppσ σ)]
  [(ppψ (par ψ_0 ψ_1))
   ,(pp-par "par" (term (ppψ ψ_0))
                  (term (ppψ ψ_1)))])

(define-metafunction coreLang
  ; ppα : α -> Doc
  [(ppα α)
   ,(above**
     (map (λ (h)
            (match h
              [(list name l m)
               (beside*/space (symbol->string name)
                              (term (ppι-var ,l))
                              (term (ppMod ,m)))]))
          (term α)))])

(define (pp-par label left right)
  (above*
   label
   (beside "{{{ " left)
   "\\\\\\"
   (indent (string-length "{{{ ")
           (beside right " }}}"))))

(define-metafunction coreLang
  ; ppφ : φ -> Doc
  [(ppφ α) (ppα α)]
  [(ppφ (par φ_0 φ_1))
   ,(pp-par "par" (term (ppφ φ_0))
                  (term (ppφ φ_1)))])

; -----
(define-metafunction coreLang
  ; ppStateη : auxξ -> Doc
  [(ppStateη (θ_0 ... η θ_1 ...))
   ,(above* "--- η" (term (ppη η)))]
  [(ppStateη auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStateψ : auxξ -> Doc
  [(ppStateψ (θ_0 ... (Read ψ) θ_1 ...))
   ,(above* "--- Read ψ" (term (ppψ ψ)))]
  [(ppStateψ auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStateσ : auxξ -> Doc
  [(ppStateσ (θ_0 ... (SC σ) θ_1 ...))
   ,(above* "--- SC σ" (term (ppσ σ)))]
  [(ppStateσ auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStateφ : auxξ -> Doc
  [(ppStateφ (θ_0 ... (P φ) θ_1 ...))
   ,(above* "--- P φ" (term (ppφ φ)))]
  [(ppStateφ auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ;ppState : auxξ -> Doc
  [(ppState auxξ)
   ,(above* (term (ppStateη auxξ))
            (term (ppStateψ auxξ))
            (term (ppStateσ auxξ))
            (term (ppStateφ auxξ)))])

(define (write-text-state t txt)
  (send txt insert
    (doc->string
     (above* (term (pp ,(list-ref t 0))) ""
             (term (ppState ,(list-ref t 1)))))))

(define (node-to-graphviz-doc node)
  (match node
    [`(,number skip)
     (beside* (number->string number)
              " [shape=plaintext] [label=\"skip\"];")]
    [`(,number (read ,RM ,ι-var ,μ-value))
     (beside* (number->string number)
              " [shape=plaintext] [label=\"Read "
              (term (ppMod ,RM)) " " (term (ppι-var ,ι-var)) " "
              (term (ppμ ,μ-value)) "\"];")]
    [`(,number (write ,WM ,ι ,μ-value ,τ))
     (beside* (number->string number)
              " [shape=plaintext] [label=\"Write "
              (term (ppMod ,WM)) " " (term (ppι-var ,ι)) " "
              (term (ppμ ,μ-value)) " "
              "(τ: " (number->string τ) ")" "\"];")]))
  
(define (nodes-to-graphviz-doc nodes)
  (above** (map node-to-graphviz-doc nodes)))

(define (relation-to-graphviz-label relation)
  (match relation
    [`sb "[label=<<font color=\"black\">sb</font>>, color=\"black\"];"]
    [`rf "[label=<<font color=\"red\">rf</font>>, color=\"red\", constraint=\"false\"];"]
    [`sw "[label=<<font color=\"green\">sw</font>>, color=\"green\", constraint=\"false\"];"]
    [`sc "[label=<<font color=\"blue\">sc</font>>, color=\"blue\", constraint=\"false\"];"]))

(define (edge-to-graphviz-doc edge)
  (match edge
    [`(,number_0 ,number_1 ,relation)
     (beside* (number->string number_0) " -> " (number->string number_1) " "
              (relation-to-graphviz-label relation))]))

(define (edges-to-graphviz-doc edges)
  (above** (map edge-to-graphviz-doc edges)))

(define (graph-to-graphviz g)
  (match g
    [`(,nodes ,edges)
     (doc->string
      (above*
       "digraph {"
       "fontsize=10 label=\"\";"
       (indent 2 (nodes-to-graphviz-doc nodes))
       (indent 2 (edges-to-graphviz-doc edges))
       "}"))]))

#|
(define (dot-graph-render g)
  (define-values (dot-input-in  dot-input-out ) (make-pipe))
  (define-values (dot-output-in dot-output-out) (make-pipe))
  (thread (λ ()
            (fprintf dot-input-out (graph-to-graphviz g))
            ;(fprintf (current-output-port) (graph-to-graphviz g))
            ;(fprintf (current-output-port) "\n\n")
            (close-output-port dot-input-out)))
  (thread (λ ()
            (parameterize ([current-output-port dot-output-out]
                           [current-input-port  dot-input-in])
              (system "dot  -Gdpi=75 -T png"))              
            (close-output-port dot-output-out)))
  (read-bitmap dot-output-in))

(define (put-graph-image txt t)
  (let [(g (term (getGR ,(list-ref t 1))))]
   (send txt insert (make-object image-snip% (dot-graph-render g)))))
|#

(define (put-graph-text txt t)
  (let [(g (term (getGR ,(list-ref t 1))))]
   (send txt insert (graph-to-graphviz g))))

(define-metafunction coreLang
  has-graph : ξ -> boolean
  [(has-graph (AST (θ_0 ... (Graph G) θ_1 ...))) #t]
  [(has-graph ξ)                                 #f])

(define pretty-printer
  (λ (t port w txt)
    (if (not (term (has-graph ,t)))
        (write-text-state t txt)
        (begin
         (write-text-state t txt)
         (send txt insert "\n\n")
         ;(put-graph-image txt t)
         (put-graph-text txt t)
         ))))

(define-term defaultState (()))
(define-metafunction coreLang
  spwST : path auxξ -> auxξ
  [(spwST path auxξ) auxξ])
(define-metafunction coreLang
  joinST : path auxξ -> auxξ
  [(joinST path auxξ) auxξ])

(define step (define-coreStep defaultState spwST joinST isReadQueueEqualTo_t))
;(traces step (term (,testTerm5 defaultState))
;        #:pp pretty-printer)
