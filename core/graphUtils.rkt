#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(require "coreLang.rkt")
(require "coreUtils.rkt")
(provide addReadNode
         ; only for testing
         prevNodesOnThread_num addSWedges
)

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
  getι : Action -> ι
  [(getι (read  RM ι μ-value              )) ι]
  [(getι (write WM ι μ-value             τ)) ι]
  [(getι (rmw   SM ι μ-value_0 μ-value_1 τ)) ι])

(define-metafunction coreLang
  getμ-value : Action -> μ-value
  [(getμ-value (read  RM ι μ-value              )) μ-value]
  [(getμ-value (write WM ι μ-value             τ)) μ-value]
  [(getμ-value (rmw   SM ι μ-value_0 μ-value_1 τ)) μ-value])

(define-metafunction coreLang
  ;getMO : Action -> RM, WM, SM 
  [(getMO (read  RM ι μ-value              )) RM]
  [(getMO (write WM ι μ-value             τ)) WM]
  [(getMO (rmw   SM ι μ-value_0 μ-value_1 τ)) SM])

(define-metafunction coreLang
  addSWedges : number G -> G
  [(addSWedges number (Nodes Edges)) (Nodes Edges_new)
                                     (where (Just Action)
                                            ,(getActionByNumber (term number) (term Nodes)))
                                     (where ι       (getι       Action))
                                     (where μ-value (getμ-value Action))
                                     ; TODO -- add case then read from a 'rmw' action
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
                                                     (term Edges)))

                                     (side-condition (term (mo<=? acq (getMO Action))))]
  [(addSWedges number G) G])

(define-metafunction coreLang
  getWriteNumber : τ ι Nodes -> Maybe ;number
  [(getWriteNumber τ ι ()) None]
  [(getWriteNumber τ ι ((number (write WM ι μ-value τ)) Node ...))
   (Just number)]
  [(getWriteNumber τ ι ((number (rmw SM ι μ-value_0 μ-value_1 τ)) Node ...))
   (Just number)]
  [(getWriteNumber τ ι ((number Action) Node ...))
   (getWriteNumber τ ι (Node ...))])

#|
(define (addReadNode τ action path auxξ)
  (let [(G (term (getGR ,auxξ)))]
    (match G [`(,nodes ,edges)
       (let [(number_new (getNextNodeNumber nodes))]
       (let [(node_read `(,number_new ,action))]
       (let [()])))])))
|#

(define-metafunction coreLang
  addReadNode : τ Action path auxξ -> auxξ
  [(addReadNode τ Action path auxξ)
                (updateState (Graph G) (Graph G_new)
                             (updateState (GFront GF) (GFront GF_new) auxξ))
                   (where (any_0 ... (Graph G) any_1 ... (GFront GF) any_2 ...) auxξ)
                   (where (Nodes Edges) G)
                   (where number_new ,(getNextNodeNumber (term Nodes)))
                   (where Node_read (number_new Action))

                   (where number_old (getByPath path GF))
                   (where (Just number_write) (getWriteNumber τ (getι Action) Nodes))
                   (where Nodes_new ,(cons (term Node_read) (term Nodes)))
                   (where Edges_rf  ,(append
                                      (term
                                       ((number_old   number_new sb)
                                        (number_write number_new rf)))
                                      (term Edges)))

                   (where G_rf   (Nodes_new Edges_rf))
                   (where G_new  (addSWedges number_new G_rf))
                   (where GF_new (updateOnPath path number_new GF))]
  [(addReadNode τ Action path auxξ) auxξ])
