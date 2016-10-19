#lang racket
(require redex/reduction-semantics)
(require "syntax.rkt")
(require "coreUtils.rkt")
(provide (all-defined-out))
;; (provide coreLang define-coreStep define-coreTest normalize isUsed
;;          isPossibleE isPossiblePath
;;          isPossibleRead
;;          isLocationDeallocated

;;          getη isLocationUninitialized)

(define nonPostponedReadConst (term None))

(define-metafunction coreLang
  snocT : any (any ...) -> (any ...)
  [(snocT any_0 any_1) (appendT any_1 (any_0))])

(define-metafunction coreLang
  snocOnPath : path any any -> any
  [(snocOnPath () any_0 any_1) (snocT any_0 any_1)]
  [(snocOnPath (L path) any_0 (par any_1 any_2)) (par (snocOnPath path any_0 any_1) any_2)]
  [(snocOnPath (R path) any_0 (par any_1 any_2)) (par any_1 (snocOnPath path any_0 any_2))])

(define-metafunction coreLang
  snocOnPathIfNew : path any any -> any
  [(snocOnPathIfNew () any_0 any_1)
   ,(if (member (term any_0) (term any_1))
        (term any_1)
        (term (snocT any_0 any_1)))]
  [(snocOnPathIfNew (L path) any_0 (par any_1 any_2))
   (par (snocOnPathIfNew path any_0 any_1) any_2)]
  [(snocOnPathIfNew (R path) any_0 (par any_1 any_2))
   (par any_1 (snocOnPathIfNew path any_0 any_2))])

(define-metafunction coreLang
  isPossiblePath : path auxξ -> boolean
  [(isPossiblePath path (in-hole El (Paths ((path None) any ...)))) #t]

  [(isPossiblePath path (in-hole El (Paths any))) #f]
  [(isPossiblePath path auxξ) #t])

(define-metafunction coreLang
  isPossiblePath_resolve : (vName ifContext) path auxξ -> boolean
  [(isPossiblePath_resolve (vName ifContext) path
                           (in-hole El (Paths ((path (resolve vName ifContext)) any ...))))
   #t]

  [(isPossiblePath_resolve (vName ifContext) path (in-hole El (Paths any))) #f]
  [(isPossiblePath_resolve (vName ifContext) path auxξ) #t])

(define-metafunction coreLang
  isPossibleE : E auxξ -> boolean
  [(isPossibleE E auxξ) (isPossiblePath (pathE E) auxξ)])

(define-metafunction coreLang
  isPossibleEEif : E Eif auxξ -> boolean
  [(isPossibleEEif E Eif auxξ) (isPossiblePathIfContext (pathE E) (eifToIfContext Eif) auxξ)])

(define-metafunction coreLang
  isPossiblePathIfContext : path ifContext auxξ -> boolean
  [(isPossiblePathIfContext path ()
                            (in-hole El (Paths ((path None)) any ...)))
   #t]

  [(isPossiblePathIfContext path ifContext
                            (in-hole El (Paths ((path (postpone ifContext)) any ...))))
   #t]

  [(isPossiblePathIfContext path ifContext (in-hole El (Paths any))) #f]
  [(isPossiblePathIfContext path ifContext auxξ) #t])

(define-metafunction coreLang
  isPossibleτ : τ τ τ ι η -> boolean
  [(isPossibleτ τ_read τ_front τ_shift ι η)
   ,(equal? (term τ_read)
            (min (term τ_max)
                 (+ (term τ_front) (term τ_shift))))
   (where τ_max (getLastTimestamp ι η))])

(define-metafunction coreLang
  isReadPEntryLbl : pentryLbl -> boolean
  [(isReadPEntryLbl (read any ...)) #t]
  [(isReadPEntryLbl any           ) #f])

(define-metafunction coreLang
  getActionVName : pentryLbl -> vName
  [(getActionVName (read    vName any ...)) vName]
  [(getActionVName (resolve vName any ...)) vName])

(define-metafunction coreLang
  getActionτ : pentryLbl -> τ
  [(getActionτ (read τ)) τ]
  [(getActionτ (read vName τ any ...)) τ])

(define-metafunction coreLang
  getActionIfContext : pentryLbl -> ifContext
  [(getActionIfContext (read vName τ  ifContext)) ifContext]
  [(getActionIfContext (postpone      ifContext)) ifContext]
  [(getActionIfContext (resolve vName ifContext)) ifContext])

(define-metafunction coreLang
  ;; isPossibleRead : (E | path) vName ι τ τ ifContext auxξ -> boolean 
  [(isPossibleRead path vName ι τ_front τ_read ifContext
                   (θ_0 ... η θ_1 ... (Paths ((path (read vName τ_shift ifContext)) any ...)) θ_2 ...))

   (isPossibleτ τ_read τ_front τ_shift ι η)]

  [(isPossibleRead E vName ι τ_front τ_read ifContext auxξ)
   (isPossibleRead (pathE E) vName ι τ_front τ_read auxξ)]

  [(isPossibleRead any_0 vName ι τ_0 τ_1 ifContext (in-hole El (Paths any))) #f]
  [(isPossibleRead any_0 vName ι τ_0 τ_1 ifContext auxξ                    ) #t])

(define-metafunction coreLang
  isUsed : vName AST -> boolean
  [(isUsed vName AST) #f
                      (side-condition (equal? (term (subst vName 1 AST)) (term AST)))]
  [(isUsed vName AST) #t])

(define-metafunction coreLang
  ;; incPaths : (L|R) paths -> paths
  [(incPaths any paths)
   ,(map (λ (x) (list (term any) x))
         (term paths))])

(define-metafunction coreLang
  reducableThreads : AST -> paths
  [(reducableThreads (ret μ-value)) ()]
  [(reducableThreads (AST >>= K)) (reducableThreads AST)]
  [(reducableThreads (par (ret μ-value_0)
                          (ret μ-value_1)))
                     (())]

  [(reducableThreads nofuel) ()]
  [(reducableThreads stuck ) ()]

  [(reducableThreads (par AST_0 AST_1))
   ,(append (term (incPaths L paths_left ))
            (term (incPaths R paths_right)))
   (where paths_left  (reducableThreads AST_0))
   (where paths_right (reducableThreads AST_1))]

;; Default case --- the current thread is reducable.
  [(reducableThreads AST) (())])

(define-metafunction coreLang
  possibleTasks : AST auxξ -> pathsτ
  [(possibleTasks AST auxξ) (possibleTasks-path () AST auxξ)])

(define-metafunction coreLang
  isPostponedEntryIfIdentifier : any postponedEntry -> boolean
  [(isPostponedEntryIfIdentifier vName (if vName   any_1 ...)) #t]
  [(isPostponedEntryIfIdentifier vName (if vName_1 Expr α_0 α_1))
   ,(or (term (isIfInα vName α_0))
        (term (isIfInα vName α_1)))]
  [(isPostponedEntryIfIdentifier any_0 any_1               ) #f])

(define-metafunction coreLang
  ;; Checks if there is a postponed operation with the `any' identifier
  ;; (the first argument).
  isIfInα : any α -> boolean
  [(isIfInα any α) ,(ormap (λ (x)
                             (term (isPostponedEntryIfIdentifier any ,x)))
                           (term α))])

(define-metafunction coreLang
  possibleTasks-path-ifContext : AST path ifContext α auxξ -> pathsτ
  [(possibleTasks-path-ifContext (write rlx ι-var μ)         path ifContext α auxξ)
   ((path (postpone ifContext)))]
  [(possibleTasks-path-ifContext ((ret μ) >>= (λ vName AST)) path ifContext α auxξ)
   ((path (postpone ifContext)))]

  [(possibleTasks-path-ifContext (read RM ι-var) path ifContext α auxξ)
   ((path (postpone ifContext)))]
  [(possibleTasks-path-ifContext (readCon RM ι-var σ-dd) path ifContext α auxξ)
   ((path (postpone ifContext)))]

  [(possibleTasks-path-ifContext (AST >>= K) path ifContext α auxξ)
   (possibleTasks-path-ifContext  AST        path ifContext α auxξ)]

  [(possibleTasks-path-ifContext (if Expr AST_0 AST_1) path ifContext α auxξ)
   ((path (postpone ifContext)))
   (side-condition (not (term (isIfInα Expr α))))]

  [(possibleTasks-path-ifContext (if vName AST_0 AST_1) path ifContext (in-hole El (if vName Expr α_0 α_1)) auxξ)
   (appendT3 (possibleTasks-path-ifContext AST_0 path ifContext_new α_0 auxξ)
             (possibleTasks-path-ifContext AST_1 path ifContext_new α_1 auxξ)
             ,(if (redex-match coreLang number (term Expr))
                  (term (path (resolve vName ifContext)))
                  '()))

   (where ifContext_new (appendT ifContext (vName)))]

  [(possibleTasks-path-ifContext AST path ifContext α auxξ) ()])

(define-metafunction coreLang
  possibleTasks-path : path AST auxξ -> pathsτ
  [(possibleTasks-path path (ret μ) auxξ) (possibleResolvePostOps path auxξ)]

  [(possibleTasks-path path ((ret μ-subst) >>= K) auxξ)
   ,(cons (term (path None))
          (term (possibleResolvePostOps path auxξ)))]
  [(possibleTasks-path path ((ret μ) >>= K) auxξ)
   ,(cons (term (path (postpone ())))
          (term (possibleResolvePostOps path auxξ)))]

  [(possibleTasks-path path (AST >>= K) auxξ) (possibleTasks-path path AST auxξ)]

  [(possibleTasks-path path AST auxξ)
   (possibleTasks-path-read path ι RM auxξ)
   (side-condition (term (noPostponedOps auxξ)))
   (where (Just (ι RM)) (ιModFromReadAction AST))]

  [(possibleTasks-path path (par AST_0 AST_1) auxξ)
   ,(if (and (null? (term pathsτ_left ))
             (null? (term pathsτ_right)))
        (term ((path None)))
        (append (term pathsτ_left )
                (term pathsτ_right)))
   (where pathsτ_left  (possibleTasks-path (updatePath L path) AST_0 auxξ))
   (where pathsτ_right (possibleTasks-path (updatePath R path) AST_1 auxξ))]

  [(possibleTasks-path path nofuel auxξ) ()]
  [(possibleTasks-path path stuck  auxξ) ()]
  
  [(possibleTasks-path path (if vName AST_0 AST_1) auxξ)
   (appendT3 (possibleTasks-path-ifContext AST_0 path (vName) α_0 auxξ)
             (possibleTasks-path-ifContext AST_1 path (vName) α_1 auxξ)
             ,(if (redex-match coreLang number (term Expr))
                  (term (path (resolve vName ())))
                  '()))
   
   (where α (getByPath path (getφ auxξ)))
   (where (in-hole El (if vName Expr α_0 α_1)) α)]

  [(possibleTasks-path path (spw AST_0 AST_1) auxξ)
   ,(if (null? (term pathsτ_post))
        (list (term (path None)))
        (term pathsτ_post))
   (where pathsτ_post (possibleResolvePostOps path auxξ))]

;; Default case --- the current thread is reducable.
  [(possibleTasks-path path AST auxξ)
   (consT (path None) pathsτ_post)
   (where pathsτ_post (possibleResolvePostOps path auxξ))])

(define-metafunction coreLang
  ιModFromReadAction : AST -> Maybe
  [(ιModFromReadAction (read      RM ι     )) (Just (ι RM))]
  [(ιModFromReadAction (readCon   RM ι σ-dd)) (Just (ι RM))]
  [(ιModFromReadAction (cas    SM FM ι     )) (Just (ι SM))] ;; TODO: 
  [(ιModFromReadAction (casCon SM FM ι σ-dd)) (Just (ι SM))] ;; Maybe smth other then SM.
  [(ιModFromReadAction AST) None])

(define-metafunction coreLang
  noPostponedOps : auxξ -> boolean
  [(noPostponedOps (θ_0 ... (P φ) θ_1 ...)) #f]
  [(noPostponedOps auxξ) #t])

(define-metafunction coreLang
  possibleTasks-path-read : path ι RM auxξ -> pathsτ

  [(possibleTasks-path-read path ι RM auxξ)
   ,(map (λ (t)
           (term (path (read ,(- t (term τ_front))))))
     (range (term τ_front) (+ 1 (term τ_max))))
   (where σ_read (getReadσ path auxξ))
   (where τ_sc_min ,(if (equal? (term RM) 'sc)
                        (term (fromMaybe 0 (lookup ι (getσSC auxξ))))
                        0))
   (where τ_front ,(max (term τ_sc_min)
                        (term (fromMaybe 0 (lookup ι σ_read)))))
   (where τ_max (getLastTimestamp ι (getη auxξ)))])

(define-metafunction coreLang
  possibleResolvePostOps : path auxξ -> pathsτ
  [(possibleResolvePostOps path auxξ) ()
   (side-condition (term (noPostponedOps auxξ)))]
  [(possibleResolvePostOps path auxξ) (possibleResolvePostOps_α α path () auxξ )
   (where α (getByPath path (getφ auxξ)))])

(define-metafunction coreLang
  possibleResolvePostOps_α : α path ifContext auxξ -> pathsτ
  [(possibleResolvePostOps_α α path ifContext auxξ) 
   ,(apply append
           (map (λ (x)
                  (term (possibleResolvePostOps_pentry ,x path ifContext auxξ)))
                (term α)))])

(define-metafunction coreLang
  possibleResolvePostOps_pentry : postponedEntry path ifContext auxξ -> pathsτ

  [(possibleResolvePostOps_pentry (let-in vName μ-value) path ifContext auxξ)
   ((path (resolve vName ifContext)))]

  [(possibleResolvePostOps_pentry (write vName ι WM μ-value) path ifContext auxξ)
   ((path (resolve vName ifContext)))

   (where α (getByPath path (getφ auxξ)))
   (side-condition (term (canPostponedWriteBePerformed (vName ι) α)))]

  [(possibleResolvePostOps_pentry (read vName ι RM σ-dd) path ifContext auxξ)
   ,(map (λ (t) (term (path (read vName ,(- t (term τ_front)) ifContext))))
     (filter (λ (t) (term
                     (canPostponedReadBePerformed (vName ι RM σ-dd) σ_read α ifContext γ ,t)))
             (range (term τ_front) (+ 1 (term τ_max)))))
   
   (where α       (getByPath path (getφ auxξ)))
   (where γ       (getγ auxξ))
   (where σ_read  (getReadσ path auxξ))
   (where τ_front (fromMaybe 0 (lookup ι σ_read)))
   (where τ_max   (getLastTimestamp ι (getη auxξ)))]

  [(possibleResolvePostOps_pentry (if vName Expr α_0 α_1) path ifContext auxξ)
   (appendT (possibleResolvePostOps_α α_0 path ifContext_new auxξ)
            (possibleResolvePostOps_α α_1 path ifContext_new auxξ))
   (where ifContext_new (appendT ifContext (vName)))]
  
  [(possibleResolvePostOps_pentry postponedEntry path ifContext auxξ) ()])

;; Returns random element from the list.
(define select-random
  (lambda (ls)
    (let ((len (length ls)))
      (list-ref ls (random len)))))

(define-metafunction coreLang
  isSchedulerQueueEmpty : auxξ -> boolean
  [(isSchedulerQueueEmpty (θ_0 ... (Paths ()) θ_1 ...)) #t]
  [(isSchedulerQueueEmpty auxξ) #f])

(define-metafunction coreLang
  normalize_subst : ξ -> ξ
  [(normalize_subst
     ((in-hole E ((ret μ-subst) >>= (λ vName AST))) auxξ))
   (normalize_subst
     ((in-hole E (subst vName μ-subst AST))         auxξ))
   (side-condition (not (term (isUsed vName AST))))]

  [(normalize_subst (AST auxξ)) ((normalize_expr AST) auxξ)])


(define-metafunction coreLang
  normalize_expr : AST -> AST

  [(normalize_expr (in-hole E (in-hole EU μ    )))
   (normalize_expr (in-hole E (in-hole EU μ_new)))

   (where μ_new (calcμ μ))
   (side-condition (not (equal? (term μ) (term μ_new))))]

  [(normalize_expr AST) AST])

(define-metafunction coreLang
  schedulerStep : auxξ -> auxξ
  [(schedulerStep (θ_0 ... (Paths ()) θ_1 ...))
   (θ_0 ... (Paths ()) θ_1 ...)]
  [(schedulerStep (θ_0 ... (Paths pathsτ) θ_1 ...))
   (θ_0 ... (Paths ,(cdr (term pathsτ))) θ_1 ...)]
  [(schedulerStep auxξ) auxξ])

(define-metafunction coreLang
  normalize : ξ -> ξ
  [(normalize (AST auxξ)) (normalize_subst (AST (schedulerStep auxξ)))])

(define-metafunction coreLang
  isLocationDeallocated : ι-var auxξ -> boolean
  [(isLocationDeallocated ι (θ_0 ... (Deallocated listι) θ_1 ...))
   ,(not (false? (member (term ι) (term listι))))]
  [(isLocationDeallocated ι-var auxξ) #f])

(define-metafunction coreLang
  deallocate : ι auxξ -> auxξ
  [(deallocate ι (θ_0 ... (Deallocated listι) θ_1 ...))
   (θ_0 ... (Deallocated ,(cons (term ι) (term listι))) θ_1 ...)])

(define-metafunction coreLang
  isLocationUninitialized : ι-var σ-dd path auxξ -> boolean
  [(isLocationUninitialized ι σ-dd path auxξ)
   ,(or (equal? (term (getLastTimestamp ι η)) (term -1))
        (equal? (term None)
                (term (lookup ι
                              (frontMerge σ-dd (getReadσ path auxξ))))))
   (where η (getη auxξ))]
  [(isLocationUninitialized vName σ-dd path auxξ) #f])

; ST stands for `state transformer`.
(define-syntax-rule (define-coreStep defaultState)
  (begin

  (reduction-relation coreLang #:domain ξ
   
   (--> (AST     auxξ)
        (AST_new auxξ)
        "calc_expr"
        (where AST_new (normalize_expr AST))
        (side-condition (not (equal? (term AST) (term AST_new)))))

   (-->  ((in-hole E (in-hole Eif ((ret μ-subst) >>= (λ vName AST)))) auxξ)
        (normalize
         ((in-hole E (in-hole Eif (subst vName μ-subst AST)))         auxξ))
        ">>=-subst"
        (side-condition (term (isPossibleE E auxξ))))
   
   (-->  ((in-hole E (in-hole EU (in-hole EU2 (choice number_1 number_2)))) auxξ)
        (normalize
         ((in-hole E (in-hole EU (in-hole EU2         number_1          ))) auxξ))
        "num-choice-left"
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (in-hole EU (in-hole EU2 (choice number_1 number_2)))) auxξ)
        (normalize
         ((in-hole E (in-hole EU (in-hole EU2                  number_2 ))) auxξ))
        "num-choice-right"
        (side-condition (term (isPossibleE E auxξ))))
  
   (-->  ((in-hole E (                            repeat AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeat AST))))) auxξ))
        "repeat-unroll"
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (                            repeatFuel number     AST))    auxξ)
        (normalize
         ((in-hole E (AST >>= (λ x (if x (ret x) (repeatFuel number_new AST))))) auxξ))
        "repeatFuel-unroll"
        (where number_new ,(- (term number) 1))
        (side-condition
         (> (term number) 0))
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (repeatFuel 0 AST)) auxξ)
        (nofuel defaultState)
        "repeatFuel-nofuel"
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (cas SM FM ι-var μ-value_1 μ-value_2)) auxξ)
        (stuck defaultState)
        "cas-stuck-uninitialized"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var () path auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-wrong-modificators"
        (side-condition (not (term (casMO=>? SM FM)))))

   (--> ((in-hole E (casCon SM FM ι-var μ-value_1 μ-value_2 σ-dd)) auxξ)
        (stuck defaultState)
        "casCon-stuck-uninitialized"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var σ-dd path auxξ))
                            (term (isLocationDeallocated ι-var auxξ)))))

   (--> ((in-hole E (read RM ι-var)) auxξ)
        (stuck defaultState)
        "read-stuck"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var () path auxξ))
                            (term (isLocationDeallocated   ι-var auxξ)))))

   (--> ((in-hole E (readCon RM ι-var σ-dd)) auxξ)
        (stuck defaultState)
        "readCon-stuck"
        (where path (pathE E))
        (side-condition (or (term (isLocationUninitialized ι-var σ-dd path auxξ))
                            (term (isLocationDeallocated   ι-var auxξ)))))

   (--> ((in-hole E (write WM ι)) auxξ)
        (stuck defaulState)
        "write-stuck" ; segfault
        (side-condition (term (isLocationDeallocated ι-var auxξ))))
  
   (-->  ((in-hole E (if 0 AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E AST_1             ) auxξ))
        "if-false"
        (side-condition (term (isPossibleE E auxξ))))
   (-->  ((in-hole E (if number AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E AST_0                  ) auxξ))
        "if-true"
        (side-condition
          (not (equal? (term number) 0)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (par (ret μ-value_0) (ret μ-value_1)))              auxξ)
        (normalize 
         ((in-hole E (ret (    μ-value_0       μ-value_1))) (joinST path auxξ)))
        "join"
        (where path (pathE E))
        (side-condition (term (isReadQueueEqualTo (par () ()) path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (spw AST_0 AST_1)) auxξ)
        (normalize 
         ((in-hole E (par AST_0 AST_1)) auxξ_new))
        "spw"
        (where path (pathE E))
        (where auxξ_new (spwST path auxξ))
        (side-condition (term (isReadQueueEqualTo () path auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
     
   ; For test results brevity only.
   (--> ((ret μ-value) auxξ)
        ((ret μ-value) defaultState)
        "heap-info-erasure"
        (side-condition     ; To eliminate cycle.
         (not (equal? (term auxξ) (term defaultState)))))
        ;; (side-condition (term (isPossibleE E auxξ))))

   (-->  ((in-hole E (dealloc ι)) auxξ)
        (normalize
         ((in-hole E (ret     0)) auxξ_new))
        "deallocate"
        (where auxξ_new (deallocate ι auxξ))
        (side-condition (not (term (isLocationDeallocated ι auxξ))))
        (side-condition (term (isPossibleE E auxξ))))

   (--> ((in-hole E (dealloc ι)) auxξ)
        (stuck defaultState)
        "deallocate-stuck"
        (side-condition (term (isLocationDeallocated ι auxξ)))
        (side-condition (term (isPossibleE E auxξ))))
  
   ;; (--> (AST auxξ)
   ;;      (AST auxξ_new)
   ;;      "schedule-next-step"
   ;;      (side-condition (term (isSchedulerQueueEmpty auxξ)))
        
   ;;      (where pathsτ   (possibleTasks AST auxξ))
   ;;      (side-condition (not (null? (term pathsτ))))
   ;;      (where pathτ    ,(select-random (term pathsτ)))

   ;;      ;; (where τ_rand          ,(random 10))
   ;;      ;; (where paths_reducable (reducableThreads AST))
   ;;      ;; (side-condition        (not (null? (term paths_reducable))))
   ;;      ;; (where path            ,(select-random
   ;;      ;;                          (term paths_reducable)))

   ;;      ;; (where Maybe_read     (term nonPostponedReadConst)) 
        
   ;;      (where auxξ_new (updateState (Paths ())
   ;;                                   ;; (Paths ((path τ_rand Maybe_read)))
   ;;                                   (Paths (pathτ))
   ;;                                   ;; (Paths ( (() 0 None)) )
   ;;                                   auxξ)))
   )))

;;;;;;;;;;;;;;;;
; Test macros
;;;;;;;;;;;;;;;;

(define testTerm-112
  (term ((spw (ret (+ 1 2)) (ret (+ 3 9))) >>= (λ v
          (ret v)))))

#|
ret 5 < 5
|#
(define testTerm-2 (term ((ret (< 5 5)) >>= (λ x (ret x)))))


(define-syntax-rule (define-coreTest step defaultState)
  (begin
(test-->> step
          (term (,testTerm-112 defaultState))
          (term ((ret (3 12)) defaultState)))
(test-->> step
          (term (,testTerm-2 defaultState))
          (term ((ret 0) defaultState)))
))
