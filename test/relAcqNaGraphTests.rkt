#lang at-exp racket
(require redex/reduction-semantics)
(require "../core/syntax.rkt")
(require "../core/coreLang.rkt")
(require "../core/coreUtils.rkt")
(require "../rules/relAcqRules.rkt")
(require "../rules/naRules.rkt")
(require "testTerms.rkt")
(require "../core/pp.rkt")
(require "../core/graphUtils.rkt")
(require "../core/langs.rkt")
(require "../core/parser.rkt")

(define-term initialGraph  (Graph  (((0 skip)) ())))
(define-term initialGFront (GFront 0))

(define-term defaultState (() (Read ()) (NA ()) initialGraph initialGFront))

(define coreStep
  (extend-reduction-relation
   (define-coreStep defaultState)
   etaPsiGraphLang #:domain ξ))
(define coreTest (define-coreTest coreStep defaultState))

(define relAcqRules (define-relAcqRules etaPsiGraphLang))
(define naRules     (define-naRules     etaPsiGraphLang defaultState))
(define step        (union-reduction-relations coreStep relAcqRules naRules))

#|
Dekker's lock doesn't work in weak memory settings (and in our model).

               x_rel = 0;
               y_rel = 0;
x_rel = 1;         || y_rel = 1;
if y_acq == 0 then || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(test-->>∃ step testTerm4
         'stuck)

;; (traces step (term (,testTerm4 defaultState)) #:pp pretty-printer)
;; (stepper step (term (,testTerm4 defaultState)) pretty-printer)
;; (stepper step (term (,testTerm3-3 defaultState)) pretty-printer)

#|
               x_rel = 0;
               y_rel = 0;
cas_rel_acq(x, 0, 1) || cas_rel_acq(x, 0, 1)
if y_acq == 0 then   || if x_acq == 0 then
  a_na = 239            a_na = 30

It should get `stuck` because of concurrent non-atomic writes.
|#
(define term_CASif_CASif
  @prog{x_rel := 0;
        y_rel := 0;
        spw
        {{{ x_rel := 1;
            r0 := y_acq;
            if r0 == 0
            then a_na := 239
            else ret 0
            fi
        ||| y_rel := 1;
            r1 := x_acq;
            if r1 == 0
            then a_na := 30
            else ret 0
            fi }}} })

(test-->>∃ step term_CASif_CASif
         'stuck)
