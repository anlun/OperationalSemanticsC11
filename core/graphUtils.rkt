#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")

(define-metafunction coreLang
  getTimestamp : Action -> Maybe ;\tau
  [(getTimestamp (write WM ι μ-value             τ)) (Just τ)]
  [(getTimestamp (rmw   SM ι μ-value_0 μ-value_1 τ)) (Just τ)]
  [(getTimestamp Action) None])

(define-metafunction coreLang
  isWriteToLocation : ι Node -> boolean
  [(isWriteToLocation ι (number Action)) #t
                                         (where (Just τ) (getTimestamp Action))]
  [(isWriteToLocation ι Node) #f])

(define-metafunction coreLang
  isNodeτ≤τ : τ Node -> boolean
  [(isNodeτ≤τ τ_0 (number Action)) ,(<= (term τ_0)
                                        (term τ_1))
                                   (where (Just τ_1) (getTimestamp Action))])

(define (getPreviousLocationWrites writeNode nodes)
  (match writeNode
    [`(write ,WM ,ι ,μ-value ,τ)
     (filter (λ (node)
               (and (term (isWriteToLocation ,ι ,node))
                    (term (isNodeτ≤τ ,τ ,node))))
             nodes)]))

(define (getNodesByNumbers numbers nodes)
  (filter (λ (node) (match node
                      [`(,n ,action) (member n numbers)]))
          nodes))

(define (getEdgesConnectedTo number edges)
   (filter (λ (edge) (match edge
                       [`(,number0 ,number1 ,relation)
                        (= number number0)]))
            edges))

(define (getEdgesPointedBy number edges)
   (filter (λ (edge) (match edge
                       [`(,number0 ,number1 ,relation)
                        (= number number1)]))
            edges))

(define (edgeFst edge)
  (match edge
    [`(,number0 ,number1 ,relation) number0]))

(define (edgeSnd edge)
  (match edge
    [`(,number0 ,number1 ,relation) number1]))

(define (edgeRelation edge)
  (match edge
    [`(,number0 ,number1 ,relation) relation]))

(define (getNodesConnectedTo_num number edges)
  (map edgeFst (getEdgesConnectedTo number edges)))

(define (getNodesPointedBy_num number edges)
  (map edgeSnd (getEdgesPointedBy number edges)))

(define (getNodesConnectedToByRelation_num relation number edges)
  (map edgeSnd
       (filter (λ (edge) (= (edgeRelation edge) relation))
               (getEdgesConnectedTo number edges))))

(define (getNodesPointedByRelation_num relation number edges)
  (map edgeFst
       (filter (λ (edge) (= (edgeRelation edge) relation))
               (getEdgesPointedBy number edges))))

;(define connectedTo)

#|
(define-metafunction coreLang
  connectedTo : Node G -> Nodes
  [(connectedTo (number Action) (Nodes Edges))
   ,(getNodesByNumbers (term numbers) (term Nodes))
   (where numbers ,(filter (λ (x) #f #| TODO |#) (term Edges)))])
|#
;(define-metafunction coreLang
;  connectedByRelation : Relation Node G -> Nodes
;  [])

(define (prevNumsOnThread number edges)
  (match (getNodesPointedByRelation_num 'sb number edges)
    [`(,number_prev) (cons number_prev (prevNumsOnThread number_prev edges))]
    [_ '()]))

(define-metafunction coreLang
  tryAddSwEdge : number G -> G
  [(tryAddSwEdge number (Nodes Edges)) (Nodes Edges_new)
                                       (where (read RM ι μ-value)
                                              (getActionByNumber Nodes))
                                       (where ((number_write (write WM ι μ-value τ)))
                                              (getNodesPointedByByRelation rf number Edges))
                                       
                                       ;(where Nodes_prev_writes
                                       ;       (getPreviousLocationWrites
                                       ;        (term (write WM ι μ-value τ))
                                       ;        (term Nodes)))
                                       
                                       ;(where Edges_new Edges) ; TODO                                     
                                       ]
  [(tryAddSwEdge number G) G])

#|
(define (tryAddSwEdge readAction graph)
  (match (getNodesPointedByByRelation_num rf readAction edges)
      [`a graph]
      [_ (raise "More than one read-from nodes.")]))
|#

;;;;;;;;;;;;;;;;;
; Tests
;;;;;;;;;;;;;;;;;
(define-term testGraph0
  (((0 (write rel "x" 1 0))
    (1 skip)
    (2 (write rel "x" 2 1))
    (3 (write rlx "x" 3 2))
    (4 (read  acq "x" 3)))
   ((0 1 sb)
    (1 2 sb)
    (1 4 sb)
    (2 3 sb)
    (3 4 rf))))

(define-term testGraph0_with_sw
  (((0 (write rel "x" 1 0))
    (1 skip)
    (2 (write rel "x" 2 1))
    (3 (write rlx "x" 3 2))
    (4 (read  acq "x" 3)))
   ((2 4 sw)
    (0 1 sb)
    (1 2 sb)
    (1 4 sb)
    (2 3 sb)
    (3 4 rf))))

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
  (test-equal (term (tryAddSwEdge 4 testGraph0)) (term testGraph0_with_sw))
  (test-equal (term (tryAddSwEdge 3 testGraph1)) (term testGraph1)))
(graphUtils-tests) 