#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../core/langs.rkt")
(require "testTerms.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/scRules.rkt")
(require "../rules/postReadRules.rkt")

(define-term defaultState schedulerDefaultState)
(define coreStep schedulerCoreStep)

(define postponedReadRules (define-postponedReadRules schedulerLang
                             defaultState))
(define rlxWriteRules      (define-rlxWriteRules      schedulerLang
                             getWriteσ_2ψ isReadQueueEqualTo ιNotInReadQueue))
(define relAcqWriteRules   (define-relAcqWriteRules   schedulerLang
                             addReadNode_t
                             synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue 
                             addWriteNode_t))
(define naRules            (define-naWriteStuckRules  schedulerLang
                             defaultState getWriteσ_2ψ ιNotInReadQueue addWriteNode_t))
(define scRules            (define-scRules            schedulerLang
                             getReadσ updateReadσ synchronizeWriteFront isReadQueueEqualTo
                             are∀PostReadsRlx ιNotInReadQueue))
(define step (union-reduction-relations
              coreStep
              postponedReadRules
              rlxWriteRules
              relAcqWriteRules
              naRules
              scRules))

#|
  x_rlx = 0; y_rlx = 0
x_rlx  = 1 || y_rlx  = 1
R1 = y_rlx || R2 = x_rlx

Can lead to R1 = R2 = 0.
|#
(define startState
           (term (,term_WrlxRrlx_WrlxRrlx
                  (updateState (Paths ())
                               (Paths ((() 0) (() 0) (() 0)
                                       ((L ()) 0) ((R ()) 0)
                                       ((L ()) 0) ((R ()) 0)
                                       ((L ()) 0) ((R ()) 0)
                                       ((L ()) 0) ((R ()) 0)
                                       (() 0) (() 0)
                                       ))
                               defaultState))))
(test-->> step
          startState
          (term ((ret (0 0)) defaultState)))
