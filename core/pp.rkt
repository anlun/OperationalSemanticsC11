#lang racket ;/gui
(require redex/reduction-semantics)
(require racket-pretty-printing-combinators)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(provide pretty-printer ast-print print-state print-TeX)

(current-page-width 1050)
(define tabstop (make-parameter 3))
(define state-width (make-parameter 50))

(define (above** xs)
  (foldr above (empty-doc) xs))

(define (beside*/sep sep xs)
  (if (empty? xs)
      (empty-doc)
      (foldr (λ (r n) (beside* r sep n))
             (car xs)
             (cdr xs))))

(define-metafunction coreLang
  ; ppExpr : Expr -> Doc
  [(ppExpr vName ) ,(symbol->string (term vName ))]
  [(ppExpr ι     ) ι]
  [(ppExpr number) ,(number->string (term number))]
  [(ppExpr (op Expr_0 Expr_1))
   ,(beside* "("
             (term (ppExpr Expr_0)) " "
             (symbol->string (term op)) " "
             (term (ppExpr Expr_1))
             ")")])

(define-metafunction coreLang
  ; ppμ : μ -> Doc
  [(ppμ ι-var) (ppι-var ι-var)]
  [(ppμ (μ_0 μ_1))
   ,(beside*
     "[" (term (ppμ μ_0)) " " (term (ppμ μ_1)) "]")]
  [(ppμ Expr) (ppExpr Expr)]
  [(ppμ (proj1 μ))
   ,(beside (term (ppμ μ)) "_1")]
  [(ppμ (proj2 μ))
   ,(beside (term (ppμ μ)) "_2")])

(define-metafunction coreLang
  ; ppMod : WM/RM/SM/FM -> Doc
  [(ppMod rlx   ) "rlx"]
  [(ppMod con   ) "con"]
  [(ppMod acq   ) "acq"]
  [(ppMod rel   ) "rel"]
  [(ppMod sc    ) "sc" ]
  [(ppMod relAcq) "relAcq"]
  [(ppMod na    ) "na" ])

(define-metafunction coreLang
  ; ppι-var : ι-var -> string
  [(ppι-var ι) ι]
  [(ppι-var vName) ,(beside* "" (symbol->string (term vName)))])

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
 
  [(pp (dealloc ι-var))
   ,(beside*
     "dealloc "
     (term (ppι-var ι-var)))]
 
  [(pp (read RM ι-var))
   ,(beside* (term (ppι-var ι-var)) "_"
             (term (ppMod RM)))]
  
  [(pp (readCon RM ι-var σ-dd))
   ,(beside* (term (ppι-var ι-var)) "_"
             (term (ppMod RM))
             (term (ppσ σ-dd)))]

  [(pp (cas SM FM ι-var μ_0 μ_1))
   ,(beside*
     (beside* "cas_" (term (ppMod SM)) "_" (term (ppMod FM)) "(")
     (term (ppι-var ι-var)) ", "
     (term (ppμ μ_0)) ", "
     (term (ppμ μ_1)) ")")]
  
  [(pp (spw AST_0 AST_1))
   ,(pp-par "spw" (term (pp AST_0))
                  (term (pp AST_1)))]
  
  [(pp (par AST_0 AST_1))
   ,(pp-par "par" (term (pp AST_0))
                  (term (pp AST_1)))]
  
  [(pp (if Expr AST_0 AST_1))
   ,(above* (beside "if "   (term (ppExpr Expr)))
            (beside "then " (term (pp AST_0)))
            (beside "else " (term (pp AST_1)))
            "fi")]
  
  [(pp (repeat AST))
   ,(above* "repeat " (indent 2 (term (pp AST))) "end")]

  [(pp (repeatFuel number AST))
   ,(beside* "repeatFuel " (number->string (term number))
             " " (term (pp AST)) " end")]  
  
  [(pp (ret μ)) ,(beside
                  "ret "
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
                              "μ:" (term (ppμ ,n_1))
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
              [(list 'read name l m front)
               (beside*/space (term (ppι-var ,name))
                              (term (ppι-var ,l))
                              (term (ppMod   ,m))
                              (term (ppσ     ,front)))]
              [(list l name mu)
               (beside*/space (term (ppι-var ,name))
                              (term (ppμ     ,mu)))]
              [(list 'write name l m mu)
               (beside*/space (term (ppι-var ,name))
                              (term (ppι-var ,l))
                              (term (ppMod   ,m))
                              (term (ppμ     ,mu)))]))
          (term α)))])

(define (pp-par label left right)
  (above*
   label
   (beside "{{{ " left)
   "|||"
   (indent (string-length "{{{ ")
           (beside right " }}}"))))

(define-metafunction coreLang
  ; ppφ : φ -> Doc
  [(ppφ α) (ppα α)]
  [(ppφ (par φ_0 φ_1))
   ,(pp-par "par" (term (ppφ φ_0))
                  (term (ppφ φ_1)))])

(define-metafunction coreLang
  ; ppγ : γ -> Doc
  [(ppγ γ) ,(above**
             (map (λ (h)
                    (match h
                      [(list l t name)
                       (beside*/space (term (ppι-var ,l))
                                      (number->string t)
                                      (symbol->string name))]))
                  (term γ)))])

(define-metafunction coreLang
  ; ppPath : path -> Doc
  [(ppPath ()) ,"()"]
  [(ppPath (L path)) ,(beside "L" (term (ppPath path)))]
  [(ppPath (R path)) ,(beside "R" (term (ppPath path)))])

(define-metafunction coreLang
  ; ppMaybe (vName) : Maybe -> Doc
  [(ppMaybe (Just vName)) ,(symbol->string (term vName))]
  [(ppMaybe None) "None"])

(define-metafunction coreLang
  ; ppPathsτ : pathsτ -> Doc
  [(ppPathsτ pathsτ) ,(above**
             (map (λ (h)
                    (match h
                      [(list path t name)
                       (beside*/space (term (ppPath ,path))
                                      (number->string t)
                                      (term (ppMaybe ,name)))]))
                  (term pathsτ)))])

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
  ; ppStateγ : auxξ -> Doc
  [(ppStateγ (θ_0 ... (R γ) θ_1 ...))
   ,(above* "--- R γ" " " (term (ppγ γ)))]
  [(ppStateγ auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStateψ : auxξ -> Doc
  [(ppStateψWrite (θ_0 ... (Write ψ) θ_1 ...))
   ,(above* "--- Write ψ" (term (ppψ ψ)))]
  [(ppStateψWrite auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStatePathsτ : auxξ -> Doc
  [(ppStatePathsτ (θ_0 ... (Paths pathsτ) θ_1 ...))
   ,(above* "--- Paths" (term (ppPathsτ pathsτ)))]
  [(ppStatePathsτ auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppStateDealloc : auxξ -> Doc
  [(ppStateDealloc (θ_0 ... (Deallocated listι) θ_1 ...))
   ,(above* "--- Deallocated" (term (ppListι listι)))]
  [(ppStateDealloc auxξ) ,(empty-doc)])

(define-metafunction coreLang
  ; ppListι : listι -> Doc
  [(ppListι listι) ,(beside*/sep " "
                                 (map (λ (x)
                                     (term (ppι-var ,x)))
                                   (term listι)))])

(define-metafunction coreLang
  ;ppState : auxξ -> Doc
  [(ppState auxξ)
   ,(above* (term (ppStateη auxξ))
            (term (ppStateψ auxξ))
            (term (ppStateψWrite auxξ))
            (term (ppStateσ auxξ))
            (term (ppStateφ auxξ))
            (term (ppStateγ auxξ))
            (term (ppStatePathsτ  auxξ))
            (term (ppStateDealloc auxξ)))])

(define (print-state t)
  (doc->string
     (above* (term (pp ,(list-ref t 0))) ""
             (term (ppState ,(list-ref t 1))))))

(define (print-TeX t)
  (doc->string (term (ppTeX-in-listing ,t))))

(define-metafunction coreLang
  ; ppTeX-in-listing : AST -> Doc
  [(ppTeX-in-listing AST)
   ,(above* "\\begin{lstlisting}[language=while]"
            (term (ppTeX AST))
            "\\end{lstlisting}")])

(define-metafunction coreLang
  ; ppTeX-μ : μ -> Doc
  [(ppTeX-μ ι-var) (ppι-var ι-var)]
  [(ppTeX-μ (μ_0 μ_1))
   ,(beside*
     "[" (term (ppTeX-μ μ_0)) " " (term (ppTeX-μ μ_1)) "]")]
  [(ppTeX-μ Expr) (ppExpr Expr)]
  [(ppTeX-μ (proj1 μ))
   ,(beside (term (ppTeX-μ μ)) "|$_1$|")]
  [(ppTeX-μ (proj2 μ))
   ,(beside (term (ppTeX-μ μ)) "|$_2$|")])

(define-metafunction coreLang
  ; ppTeX : AST -> Doc
  [(ppTeX (spw AST_0 AST_1))
   ,(above* "\\end{lstlisting}"
            "\\begin{tabular}{l||l}"
            (above* "\\begin{lstlisting}[language=while]"
                    (term (ppTeX AST_0))
                    "\\end{lstlisting}"
                    "\\hspace{.6cm} &"
                    "\\begin{lstlisting}[language=while]"
                    (term (ppTeX AST_1))
                    "\\end{lstlisting}")
            "\\end{tabular}"
            "\\begin{lstlisting}[language=while]")]

  [(ppTeX (cas SM FM ι-var μ_0 μ_1))
   ,(beside*
     "cas|$_{" (term (ppMod SM))
     "," (term (ppMod FM)) "}$|("
     (term (ppι-var ι-var)) ", "
     (term (ppTex-μ μ_0)) ", "
     (term (ppTex-μ μ_1)) ")")]
  [(ppTeX (write WM ι-var μ))
   ,(beside*
     "|$[$|" (term (ppι-var ι-var))
     "|$]_{" (term (ppMod WM))
     "}$|"
     " = " (term (ppTeX-μ μ)))]  

  [(ppTeX (AST_0 >>= (λ vName (ret vName))))
   (ppTeX AST_0)]

  [(ppTeX (AST_0 >>= (λ vName AST_1)))
   ,(above* (beside* (term (ppTeX AST_0)) ";")
            (term (ppTeX AST_1)))
   (side-condition (equal? 'r-1 (term vName)))]

  [(ppTeX (AST_0 >>= (λ vName AST_1)))
   ,(above*
     (beside* (symbol->string (term vName))
              " = "
              (term (ppTeX AST_0))
              ";")
     (term (ppTeX AST_1)))
   (side-condition (not (equal? 'r-1 (term vName))))]
 
  [(ppTeX (read RM ι-var))
   ,(beside*
     "|$[$|" (term (ppι-var ι-var))
     "|$]_{" (term (ppMod RM))
     "}$|")]
  
  [(ppTeX (repeat AST))
   ,(above*
     "repeat"
     (indent 2 (term (ppTeX AST)))
     "end")]
  
  [(ppTeX (if μ AST_0 AST_1))
   ,(above* (beside* "if "   (term (ppTeX-μ μ)))
            (beside* "then " (term (ppTeX AST_0)))
            (beside* "else " (term (ppTeX AST_1)))
            "fi")]

  [(ppTeX (dealloc ι-var)) ,(beside* "delete " (term (ppTeX-μ ι-var)))]
  [(ppTeX (ret μ)) ,(beside "ret " (term (ppTeX-μ μ)))])

(define (write-text-state t txt)
  (send txt insert (print-state t)))

(define (ast-print ast)
  (doc->string (term (pp ,ast))))

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

(define (relation-to-color-string relation)
  (match relation
    [`sb "black"]
    [`rf "red"  ]
    [`sw "green"]
    [`sc "blue" ]))

(define (constraint-relation? relation)
  (match relation
    [`sb #t]
    [_   #f]))

(define (relation-to-label-text relation)
  (beside*
     "<font color=\""
     (relation-to-color-string relation)
     "\">"
     (symbol->string relation)
     "</font>"))

(define (relations-to-graphviz-label relations)
  (beside*
   "[label=<"
   (beside*/sep "," (map relation-to-label-text relations))
   ">, color=\""
   (beside*/sep ":" (map relation-to-color-string relations))
   "\""
   (if (ormap constraint-relation? relations)
       ""
       ", constraint=\"false\"")
   "];"))

(define (multilabel-edge-to-graphviz-doc multilabel-edge)
  (let ([start-node (car   multilabel-edge)]
        [end-node   (cadr  multilabel-edge)]
        [relations  (caddr multilabel-edge)])
   (beside* (number->string start-node)
            " -> "
            (number->string end-node)
            " "
            (relations-to-graphviz-label relations))))

(define (edges-to-graphviz-doc edges)
  (above**
   (map multilabel-edge-to-graphviz-doc
        (group-edges edges))))

(define (collinear-edges? edge_0)
  (λ (edge_1)
    (and (equal? (car  edge_0) (car  edge_1))
         (equal? (cadr edge_0) (cadr edge_1)))))

(define (group-edges edges)
  (match edges
    ['() '()]
    [_
     (let*-values ([(edge) (car edges)]
                   [(l_0 l_1) (partition (collinear-edges? edge) edges)])
       (cons
        (list
         (car edge) (cadr edge)
         (map caddr l_0))
        (group-edges l_1)))]))

(define (graph-to-graphviz g)
  (match g
    [`(,nodes ,edges)
     (doc->string
      (above*
       "digraph {"
"fontsize=10 label=\"\" splines=true overlap=true ranksep=0.2 nodesep=0.025;"
 
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
