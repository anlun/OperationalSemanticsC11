#lang racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/postReadRules.rkt")
(require "../rules/rlxRules.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "../rules/scRules.rkt")
(require "../core/langs.rkt")
(require "../test/testTerms.rkt")

(define-term defaultState (() (Read ()) (AcqFront ()) (RelFront ()) (NA ()) (Write ()) (SC ())))
(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState)
   etaPsi2SCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define rlxRules    (define-rlxRules    etaPsi2SCLang))
(define relAcqRules (define-relAcqRules etaPsi2SCLang
                      addReadNode_t
                      are∀PostReadsRlx
                      addWriteNode_t))
(define naRules     (define-naWriteStuckRules  etaPsi2SCLang
                      defaultState addWriteNode_t))
(define scRules     (define-scRules            etaPsi2SCLang
                      getReadσ updateReadσ are∀PostReadsRlx))

(define step (union-reduction-relations
              coreStep rlxRules relAcqRules naRules scRules))

(test-->> step
         (term (,testSB+rel+acq+fences+sc defaultState))
         (term ((ret (0 1)) defaultState))
         (term ((ret (1 0)) defaultState))
         (term ((ret (1 1)) defaultState)))

(test-->> step
         (term (,testSB+rlx+fences+sc defaultState))
         (term ((ret (0 1)) defaultState))
         (term ((ret (1 0)) defaultState))
         (term ((ret (1 1)) defaultState)))
