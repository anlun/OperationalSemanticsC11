#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreUtils.rkt")
(require "../core/langs.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/scRules.rkt")
(require "../rules/postReadRules.rkt")
(provide (all-defined-out))

(define-term defaultState schedulerDefaultState)
(define coreStep schedulerCoreStep)

(define postponedReadRules (define-postponedReadRules schedulerLang
                             defaultState getWriteσ_2ψ))
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

