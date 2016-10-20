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
   (define-coreStep defaultState)
   etaPsi2SCLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define rlxReadRules  (define-rlxReadRules  etaPsi2SCLang))
(define rlxWriteRules (define-rlxWriteRules etaPsi2SCLang))
(define relAcqRules   (define-relAcqRules   etaPsi2SCLang are∀PostReadsRlx))
(define naRules       (define-naRules       etaPsi2SCLang defaultState))
(define scRules       (define-scRules       etaPsi2SCLang are∀PostReadsRlx))
(define step          (union-reduction-relations
                       coreStep rlxReadRules rlxWriteRules relAcqRules naRules scRules))
