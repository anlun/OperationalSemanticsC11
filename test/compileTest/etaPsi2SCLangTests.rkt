#lang racket
(require redex/reduction-semantics)
(require "../../core/syntax.rkt")
(require "../../core/coreLang.rkt")
(require "../../core/coreUtils.rkt")
(require "../../rules/rlxRules.rkt")
(require "../../rules/relAcqRules.rkt")
(require "../../rules/naRules.rkt")
(require "../../rules/scRules.rkt")
(require "../../core/langs.rkt")

(define-term defaultState (() (Read ()) (AcqFront ()) (RelFront ()) (NA ()) (Write ()) (SC ())))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState spwST-2ψ joinST-2ψ)
   etaPsi2SCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define rlxReadRules  (define-rlxReadRules  etaPsi2SCLang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2SCLang
                        getWriteσ_2ψ))
(define relAcqRules   (define-relAcqRules   etaPsi2SCLang
                        addReadNode_t
                        synchronizeWriteFront
                        are∀PostReadsRlx
                        addWriteNode_t))
(define naRules       (define-naRules       etaPsi2SCLang
                       addReadNode_t
                       defaultState getWriteσ_2ψ
                       addWriteNode_t))
(define scRules       (define-scRules     etaPsi2SCLang
                       getReadσ updateReadσ synchronizeWriteFront
                       are∀PostReadsRlx))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules scRules))
