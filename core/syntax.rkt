#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

(define-language syntax
  [AST (ret μ)
       (AST >>= K)       ; `let-in` construction can be emulated by (ret Expr) >>= (λ x AST). 
       (write  WM ι-var μ       )
       
       ; `σ-dd` is an additional synchronization front for modeling consume accesses
       (read   RM ι-var     σ-dd)
       (cas SM FM ι-var μ μ σ-dd)
       ; Atomic read-modify-write operations shall always read the last value (in the modification order) written
       ; before the write associated with the read-modify-write operation.
       ; C++ Standard, 29.4-12, p.1101
       ; http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2012/n3337.pdf
       
       (fence FenceM)
       
       (if Expr AST AST)
       (repeat  AST    )
       (par     AST AST) ; Run-time construction.
       (spw     AST AST) ; Construction to start parallel execution.

       (dealloc ι-var)
       
       (repeatFuel number AST) ; repeat with fuel
       nofuel
       stuck]

  [K  (λ vName AST)]

  [μ Expr   ; Value
     (μ μ)
     (projOp μ)]
  
  [Expr ι-var
        number
        (op Expr Expr)]
  [op + - * / % == != > >= < <=
      choice] ; The `choice` operator will nondeterministically choose left or right expression.

  [projOp proj1
          proj2]

  [μ-value number
           (μ-value μ-value)
           ι]

  [μ-subst μ-value
           vName]
  
  [ι string] ; Location. We could have used 'number' instead of 'string'.
  [ι-var ι
         vName]

  [RM sc con acq rlx na]
  [WM sc rel rlx na]
  [SM sc relAcq acq rel rlx]
  [FM sc acq rlx]
  [FenceM sc rel acq]

  [τ number]                         ; Timestamp
  [η-cell ((τ μ-value σ) ...)]
  [η ((ι η-cell) ...)]               ; Heap history

  ; For consume propagated information.
  ; The order is important, which is why it is separated from ordinary σ.
  [σ-dd ((ι τ) ...)]

  [σ ((ι τ) ...)]         ; Single front
  ; Front invariant:
  ; For every location in front should be no more than one record.
  ; Or at least actual one must be placed first.
  
  ; Scheduler fronts for threads
  [σ-tree σ
          (par σ-tree σ-tree)]
  
  ; A function from ι to σ, which represents per-location release fronts.
  [χ ((ι σ) ...)]
  ; A per-thread χ function.
  [χ-tree χ
          (par χ-tree χ-tree)]
    
  [E hole
     (E >>= K)
     (par E AST)
     (par AST E)]
  [Ef hole
      (par Ef σ-tree)
      (par σ-tree Ef)]

  ; Expression usage
  [EU hole
      (ret EU)
      (write  WM ι-var EU)
      (cas SM FM ι-var EU μ σ-dd)
      (cas SM FM ι-var μ EU σ-dd)
      (if EU AST AST)]

  [EU2 hole
       (EU2 μ)
       (μ EU2)
       (projOp EU2)
       (op μ EU2)
       (op EU2 μ)]

  [El (any_0 ... hole any_1 ...)]
  
  [path ()
        (L path)
        (R path)]

  [ifContext (vName ...)]

  [paths  (path  ...)]
  [listι  (ι ...)]

  [Maybe (Just any)
         None]

  ;; Defintions related to postponed operations:
  [postponedEntry (read   vName ι-var RM σ-dd) ;; postponed read
                  (let-in vName μ)             ;; postponed let expression
                  (write  vName ι-var WM μ)    ;; postponed write
                  (fence  vName FenceM)
                  
                  ;; Speculative `if'.
                  ;; vName --- an unique identifier;
                  ;; Expr  --- an `if' condition;
                  ;; α's   --- postponed operations of `then' and `else' branches;
                  (if     vName Expr α α)]
  [α-tree α
          (par α-tree α-tree)]
  [α (postponedEntry ...)]
  [γ ((ι τ vName) ...)]

  ;; Speculative `if' context
  [Eif Eif1
       (if vName Eif AST)
       (if vName AST Eif)]

  [Eif1 hole
        (Eif1 >>= K)]

  [Ep hole
      (par Ep α-tree)
      (par α-tree Ep)]
  [Eifα hole
        (postponedEntry ... (if vName Expr Eifα α) postponedEntry ...)
        (postponedEntry ... (if vName Expr α Eifα) postponedEntry ...)]
  
  [observedWriteLbl (vName ι)
                    (par observedWrites observedWrites)]
  [observedWriteList (observedWriteLbl ...)]
  [observedWrites observedWriteList
                  (par observedWrites observedWrites)]


  ;; Graph related defintions:
  [Relation rf
            sb
            sw
            sc]
  [Action skip
          (write WM ι     μ-value τ) ; τ --- it's a timestamp of record in a history (η).
          (rmw   SM ι     μ-value μ-value τ)
          (read  RM ι-var μ-value)]
  
  [Node  (number Action)]
  [Nodes (Node ...)]
  [Edge  (number number Relation)]
  [Edges (Edge ...)]
  [G     (Nodes Edges)]
  
  ; GF saves a pointer to current node for every thread.
  [GF number
      (par GF GF)]
  
  [vName variable-not-otherwise-mentioned])

(current-cache-all? #t)

;  [SM sc relAcq acq rel rlx]
;  [FM sc acq rlx]
(define-metafunction syntax
  casMO=>? : SM FM -> boolean
  [(casMO=>? sc     sc ) ,#t]
  [(casMO=>? sc     acq) ,#t]
  [(casMO=>? sc     rlx) ,#t]
  [(casMO=>? relAcq acq) ,#t]
  [(casMO=>? relAcq rlx) ,#t]
  [(casMO=>? acq    acq) ,#t]
  [(casMO=>? acq    rlx) ,#t]
  [(casMO=>? rel    rlx) ,#t]
  [(casMO=>? rlx    rlx) ,#t]
  [(casMO=>? SM     FM ) ,#f])

(define (mo=>? mo1 mo2)
  (match `(,mo1 ,mo2)
    [`(,x     ,x) #t]
    [`(sc     ,_) #t]
    [`(,_     sc) #f]
    [`(relAcq ,_) #t]
    [`(,_ relAcq) #f]

    [`(rel   acq) #f]
    [`(rel   con) #f]
    [`(rel   rlx) #t]

    [`(acq   rel) #f]
    [`(acq   con) #t]
    [`(acq   rlx) #t]
    [`(con   rlx) #t]
    [_            #f]))

(define (mo<=? mo1 mo2)
  (mo=>? mo2 mo1))

(define (pair<? p q)
  (match (list p q)
    [(list (list p1 p2) (list q1 q2)) (string<? p1 q1)]))

(define-metafunction syntax
  sortσ : σ -> σ
  [(sortσ σ) ,(sort (term σ) pair<?)])

(define-metafunction syntax
  sortσ-tree : σ-tree -> σ-tree
  [(sortσ-tree σ) (sortσ σ)]
  [(sortσ-tree (par σ-tree_1 σ-tree_2)) (par (sortσ-tree σ-tree_1) (sortσ-tree σ-tree_2))])

(define-metafunction syntax
  sortη : η -> η
  [(sortη η) ,(sort (term η) pair<?)])

;; Store/environment lookup
(define-metafunction syntax
  lookup : any ((any any) ...) -> Maybe
  [(lookup any_0 ((any_0 any_1) any ...)) (Just any_1)]
  [(lookup any_2 (any_0 any_1 ...)) 
   (lookup any_2 (any_1 ...))]
  [(lookup any ()) None])

(define-metafunction syntax
  lookup3 : any ((any any any) ...) -> Maybe
  [(lookup3 any_0 ((any_0 any_1 any_2) any ...))
   (Just (any_1 any_2))]
  [(lookup3 any_2 (any_0 any_1 ...)) 
   (lookup3 any_2 (any_1 ...))]
  [(lookup3 any ()) None])

(define-metafunction syntax
  [(removeByKey any ()) ()]
  [(removeByKey any_1 ((any_1 any_3) any_4 ...))
   (removeByKey any_1 (any_4 ...))]
  [(removeByKey any_1 ((any_2 any_3) any_4 ...))
   ,(cons (term (any_2 any_3)) (term (removeByKey any_1 (any_4 ...))))])

(define-metafunction syntax
  maxMaybe : ι τ Maybe -> (ι τ)
  [(maxMaybe ι τ None)
   (ι τ)]
  [(maxMaybe ι number_1 (Just number_2))
   (ι ,(max (term number_1) (term number_2)))])

(define-metafunction syntax
  maxLookup : ι τ σ -> (ι τ)
  [(maxLookup ι τ σ)
   (maxMaybe ι τ (lookup ι σ))])

(define-metafunction syntax
  frontMerge : σ σ -> σ
  [(frontMerge () σ) σ]
  [(frontMerge σ ()) σ]
  [(frontMerge ((ι τ) any ...) σ)
   (sortσ ,(cons (term (maxLookup ι τ σ)) (term (frontMerge (any ...) (removeByKey ι σ)))))])

(define-metafunction syntax
  pathE : E -> path
  [(pathE hole) ()]
  [(pathE (E >>= K)  )    (pathE E)]
  [(pathE (par E AST)) (L (pathE E))]
  [(pathE (par AST E)) (R (pathE E))])

(define-metafunction syntax
  pathEf : Ef -> path
  [(pathEf hole) ()]
  [(pathEf (par Ef σ-tree)) (L (pathEf Ef))]
  [(pathEf (par σ-tree Ef)) (R (pathEf Ef))])

(define-metafunction syntax
  substι : vName μ ι-var -> ι-var
  [(substι vName ι-var vName) ι-var]
  [(substι vName μ     ι-var) ι-var])

(define-metafunction syntax
  subst : vName μ AST -> AST
  [(subst vName μ_1 (ret μ_2))
   (ret (substExpr vName μ_1 μ_2))]
  [(subst vName μ (AST >>= K))
   ((subst vName μ AST) >>= (substCont vName μ K))]
  
  [(subst vName μ_1 (dealloc ι-var))
   (dealloc (substι vName μ_1 ι-var))]

  [(subst vName μ_1 (read RM ι-var σ-dd))
   (read RM (substι vName μ_1 ι-var) σ-dd)]

  [(subst vName μ_1 (write WM ι-var μ_2))
   (write WM (substι vName μ_1 ι-var) (substExpr vName μ_1 μ_2))]

  [(subst vName μ_1 (cas SM FM ι-var μ_2 μ_3 σ-dd))
   (cas SM FM (substι vName μ_1 ι-var) (substExpr vName μ_1 μ_2) (substExpr vName μ_1 μ_3) σ-dd)]

  [(subst vName μ (par AST_1 AST_2))
   (par (subst vName μ AST_1) (subst vName μ AST_2))]
  [(subst vName μ (spw AST_1 AST_2))
   (spw (subst vName μ AST_1) (subst vName μ AST_2))]
  [(subst vName μ (if Expr AST_1 AST_2))
   (if (substExpr vName μ Expr) (subst vName μ AST_1) (subst vName μ AST_2))]
  [(subst vName μ (repeat AST))
   (repeat (subst vName μ AST))]
  [(subst vName μ (repeatFuel number AST))
   (repeatFuel number (subst vName μ AST))]
  [(subst vName μ AST) AST])

(define-metafunction syntax
  substCont : vName μ K -> K
  [(substCont vName_1 μ (λ vName_2 AST))
   (λ vName_2 (subst vName_1 μ AST))
   (side-condition
     (not (equal? (term vName_1) (term vName_2))))]
  [(substCont vName μ K) K])

(define-metafunction syntax
  ; substExpr : nameOfVariable exprToInsert exprToBeInsertedIn -> resultOfInsertion
  substExpr : vName μ_1 μ_2 -> μ_3
  [(substExpr vName μ vName) μ]
  [(substExpr vName μ_1 (projOp μ_2))
   (projOp (substExpr vName μ_1 μ_2))]
  [(substExpr vName μ (op Expr_1 Expr_2))
   (op (substExpr vName μ Expr_1) (substExpr vName μ Expr_2))]
  [(substExpr vName μ_1 (μ_2 μ_3))
   ((substExpr vName μ_1 μ_2) (substExpr vName μ_1 μ_3))]
  [(substExpr vName μ_1 μ_2) μ_2])

(define-metafunction syntax
  getCellHistory : ι η -> η-cell
  [(getCellHistory ι ()) ()]
  [(getCellHistory ι_1 ((ι_2 ((τ μ-value σ) ...)) (ι_3 ((τ_3 μ-value_3 σ_3) ...)) ...))
   ((τ μ-value σ) ...)
   (side-condition
    (equal? (term ι_1) (term ι_2)))]
  [(getCellHistory ι_1 ((ι_2 ((τ_1 μ-value_1 σ_1) ...)) (ι_3 ((τ μ-value σ) ...)) ...))
   (getCellHistory ι_1 ((ι_3 ((τ μ-value σ) ...)) ...))])

(define-metafunction syntax
  getLastTimestampFromCellHistory : η-cell -> τ
  [(getLastTimestampFromCellHistory ()) -1]
  [(getLastTimestampFromCellHistory ((τ_1 μ-value_1 σ_1) (τ_2 μ-value_2 σ_2) ...))
   ,(max (term τ_1) (term (getLastTimestampFromCellHistory ((τ_2 μ-value_2 σ_2) ...))))
   ])

(define-metafunction syntax
  getNextTimestampFromCellHistory : η-cell -> τ
  [(getNextTimestampFromCellHistory η-cell) ,(+ 1 (term (getLastTimestampFromCellHistory η-cell)))])

(define-metafunction syntax
  getLastTimestamp : ι η -> τ
  [(getLastTimestamp ι η)
   (getLastTimestampFromCellHistory (getCellHistory ι η))])

(define-metafunction syntax
  getNextTimestamp : ι η -> τ
  [(getNextTimestamp ι η)
   (getNextTimestampFromCellHistory (getCellHistory ι η))])

(define-metafunction syntax
  updateCellWOsorting : ι μ-value σ η -> η
  [(updateCellWOsorting ι μ-value σ η)
   ,(let ([newCellHistory (cons (term ((getNextTimestamp ι η) μ-value σ)) (term (getCellHistory ι η)))]
          [historyWOι (term (removeByKey ι η))])
     (cons (list (term ι) newCellHistory) historyWOι))])

(define-metafunction syntax
  updateCell : ι μ-value σ η -> η
  [(updateCell ι μ-value σ η) (sortη (updateCellWOsorting ι μ-value (sortσ σ) η))])

(define-metafunction syntax
  updateFront : ι τ σ -> σ
  [(updateFront ι τ σ)
   (sortσ ,(cons (list (term ι) (term τ)) (term (removeByKey ι σ))))])

(define-metafunction syntax
  isNormalized : μ -> boolean

  [(isNormalized number) #t]
  [(isNormalized (μ_0 μ_1))
   ,(and (term (isNormalized μ_0))
         (term (isNormalized μ_1)))]
 
  [(isNormalized μ) #f])

(define-metafunction syntax
  calc : μ -> μ
  [(calc (+  number_0 number_1)) ,(+          (term number_0) (term number_1))]
  [(calc (-  number_0 number_1)) ,(-          (term number_0) (term number_1))]
  [(calc (*  number_0 number_1)) ,(*          (term number_0) (term number_1))]
  [(calc (/  number_0 number_1)) ,(/          (term number_0) (term number_1))]
  [(calc (%  number_0 number_1)) ,(remainder  (term number_0) (term number_1))]
  [(calc (== number_0 number_1)) ,(if (equal? (term number_0) (term number_1)) 1 0)]
  [(calc (!= number_0 number_1)) ,(if (equal? (term number_0) (term number_1)) 0 1)]
  [(calc (>  number_0 number_1)) ,(if (>      (term number_0) (term number_1)) 1 0)]
  [(calc (>= number_0 number_1)) ,(if (>=     (term number_0) (term number_1)) 1 0)]
  [(calc (<  number_0 number_1)) ,(if (<      (term number_0) (term number_1)) 1 0)]
  [(calc (<= number_0 number_1)) ,(if (<=     (term number_0) (term number_1)) 1 0)]

  [(calc (proj1 (μ_0 μ_1))) μ_0]
  [(calc (proj2 (μ_0 μ_1))) μ_1]

  [(calc (== ι_0 ι_1)) ,(if (equal? (term ι_0) (term ι_1)) 1 0)]
  [(calc (!= ι_0 ι_1)) ,(if (equal? (term ι_0) (term ι_1)) 0 1)]
  
  [(calc (== ι μ)) 0
   (side-condition (term (isNormalized μ)))]
  [(calc (!= ι μ)) 1
   (side-condition (term (isNormalized μ)))]

  [(calc (== μ ι)) (calc (== ι μ))]
  [(calc (!= μ ι)) (calc (!= ι μ))]

  [(calc μ) μ])

(define-metafunction syntax
  calcμ : μ -> μ
  [(calcμ (μ_0 μ_1))
   ((calcμ μ_0) (calcμ μ_1))]

  [(calcμ (projOp μ))
   (calc  (projOp (calcμ μ)))]

  [(calcμ (op Expr_0 Expr_1))
   (calc  (op (calcμ Expr_0) (calcμ Expr_1)))]

  [(calcμ ι-var)
   ι-var]

  [(calcμ number)
   number])

(define-metafunction syntax
  fromMaybe : any Maybe -> any
  [(fromMaybe any None) any]
  [(fromMaybe any_1 (Just any_2)) any_2])

(define-metafunction syntax
  updateFrontAfterRead : ι τ σ -> σ
  ; [(updateFrontAfterRead ι τ σ) σ] ; This version allows CoRR anomalies as SPARC RMO
  [(updateFrontAfterRead ι τ σ) (updateFront ι τ σ)])

(define-metafunction syntax
  maybeProj1 : Maybe -> Maybe
  [(maybeProj1 (Just (any_0 any_1))) (Just any_0)]
  [(maybeProj1 any) None])

(define-metafunction syntax
  maybeProj2 : Maybe -> Maybe
  [(maybeProj2 (Just (any_0 any_1))) (Just any_1)]
  [(maybeProj2 any) None])

(define-metafunction syntax
  getValueByTimestamp : ι τ η -> Maybe
  [(getValueByTimestamp ι τ η)
   ,(let ([cellHistory (term (getCellHistory ι η))])
      (term (maybeProj1 (lookup3 τ ,cellHistory))))])

(define-metafunction syntax
  getValueByCorrectTimestamp : ι τ η -> μ-value
  [(getValueByCorrectTimestamp ι τ η) (fromMaybe -1 (getValueByTimestamp ι τ η))])
  ; This `fromMaybe -1` is needed only to preserve types.
  ; getValueByTimestamp must return real value,
  ; but τ is need to be checked to be correct for that location by rule side-condition.

(define-metafunction syntax
  getFrontByTimestamp : ι τ η -> Maybe
  [(getFrontByTimestamp ι τ η)
   ,(let ([cellHistory (term (getCellHistory ι η))])
      (term (maybeProj2 (lookup3 τ ,cellHistory))))])

(define-metafunction syntax
  elToList : El -> any
  [(elToList (any_0 ... hole any_1 ...)) (any_0 ... any_1 ...)])

(define-extended-language coreLang syntax
  ; State:
  ; AST -- current state of program tree.
  [auxξ (any ... η any ...)]
  [ξ (AST auxξ)

     ; These ξ-variations exist only for convenience.
     AST
     μ-value]
  
  [listξ (ξ ...)])
