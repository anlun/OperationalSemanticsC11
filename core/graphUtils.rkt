#lang racket
(require redex)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(provide addSWedges)

(define-metafunction coreLang
  getTimestamp : Action -> Maybe ;\tau
  [(getTimestamp (write WM ι μ-value             τ)) (Just τ)]
  [(getTimestamp (rmw   SM ι μ-value_0 μ-value_1 τ)) (Just τ)]
  [(getTimestamp Action) None])

(define-metafunction coreLang
  isWriteToLocation : ι Node -> boolean
  [(isWriteToLocation ι (number (write WM ι μ-value             τ))) #t]
  [(isWriteToLocation ι (number (rmw   SM ι μ-value_0 μ-value_1 τ))) #t]
  [(isWriteToLocation ι Node) #f])

(define-metafunction coreLang
  isNodeτ≤τ : τ Node -> boolean
  [(isNodeτ≤τ τ_0 (number Action)) ,(<= (term τ_1)
                                        (term τ_0))
                                   (where (Just τ_1) (getTimestamp Action))])

(define (getPrevιWrites_num ι τ nodes)
   (map (λ (node) (match node
                    [`(,number ,action) number]))
        (filter (λ (node)
                  (and (term (isWriteToLocation ,ι ,node))
                       (term (isNodeτ≤τ ,τ ,node))))
                nodes)))

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


(define (relFilter relation edges)
  (filter (λ (edge) (equal? (edgeRelation edge) relation)) edges))

(define (getNodesConnectedToByRelation_num relation number edges)
  (map edgeSnd
       (relFilter relation
               (getEdgesConnectedTo number edges))))

(define (getNodesPointedByRelation_num relation number edges)
  (map edgeFst
       (relFilter relation
               (getEdgesPointedBy number edges))))

(define (getNodesPointedByRelation relation number nodes edges)
  (map (λ (number_pointee)
         (match (getActionByNumber number_pointee nodes)
           [`(Just ,action) `(,number_pointee ,action)]))
       (getNodesPointedByRelation_num relation number edges)))

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

(define (prevNodesOnThread_num number edges nodes)
  (match (getActionByNumber number nodes)
    ['skip '()]
    [_ (match (getNodesPointedByRelation_num 'sb number edges)
         [`(,number_prev) (match (getNodesConnectedToByRelation_num 'sb number_prev edges)
                            [`(,a) (cons number_prev (prevNodesOnThread_num number_prev edges nodes))]
                            [_ '()])]
         [_ '()])]))

(define (getActionByNumber number nodes)
  (match nodes
    [`((,cur_number ,action) ,nodes_tail ...)
     (if (equal? cur_number number)
         `(Just ,action)
         (getActionByNumber number nodes_tail))]
    [_ 'None]))

(define (getWritesToSW_num prevWrites threadOperations nodes)
  (match prevWrites
    [`(,prevWrite ,tail ...)
     (match (getActionByNumber prevWrite nodes)
       [`(Just (write ,WM ,ι ,μ-value ,τ))
        (if (member prevWrite threadOperations)
            (let [(tailResult (getWritesToSW_num tail threadOperations nodes))]
              (if (mo=>? WM 'rel)
                  (cons prevWrite tailResult)
                  tailResult))
            '())]
       [`(Just (rmw ,SM ,ι ,μ-value ,τ))
        (let [(tailResult (getWritesToSW_num tail threadOperations nodes))]
          (if (mo=>? SM 'rel)
              (cons prevWrite tailResult)
              tailResult))]
       ['None (getWritesToSW_num tail threadOperations nodes)])]
    [_ '()]))

(define (getSWedges number writesToSW)
  (map (λ (write_num) `(,write_num ,number sw)) writesToSW))

(define-metafunction coreLang
  addSWedges_graph : number G -> G
  [(addSWedges_graph number (Nodes Edges)) (Nodes Edges_new)
                                     (where (Just (read RM ι μ-value))
                                            ,(getActionByNumber (term number) (term Nodes)))                                     
                                     (where ((number_write (write WM ι μ-value τ)))
                                            ,(getNodesPointedByRelation (term rf)
                                                                        (term number)
                                                                        (term Nodes)
                                                                        (term Edges)))
                                     (where (number_writes ...)
                                            ,(sort (getPrevιWrites_num
                                                    (term ι) (term τ) (term Nodes))
                                                   (λ (x y) (>= x y))))                                     
                                     (where (number_prevThreadOperations ...)
                                            ,(prevNodesOnThread_num (term number_write)
                                                                    (term Edges)
                                                                    (term Nodes)))
                                     (where (number_threadOperations ...)
                                            ,(cons (term number_write)
                                                   (term (number_prevThreadOperations ...))))
                                     (where (number_writesToSW ...)
                                            ,(getWritesToSW_num (term (number_writes ...))
                                                                (term (number_threadOperations ...))
                                                                (term Nodes)))
                                     (where Edges_new
                                            ,(append (getSWedges (term number) (term (number_writesToSW ...)))
                                                     (term Edges)))]
  [(addSWedges_graph number G) G])

(define-metafunction coreLang
  addSWedges : number auxξ -> auxξ
  [(addSWedges number auxξ) (updateState (Graph G) (Graph G_new) auxξ)
                            (where G (getGR auxξ))
                            (where G_new (addSWedges_graph number G))])

;;;;;;;;;;;;;;;;;
; Tests
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
  (test-equal (term (addSWedges_graph 4 testGraph0)) (term testGraph0_with_sw))
  (test-equal (term (addSWedges_graph 3 testGraph1)) (term testGraph1))
  (test-equal (prevNodesOnThread_num 3 (term edges0) (term nodes0)) (term (2))))
(graphUtils-tests)