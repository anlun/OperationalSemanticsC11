#lang at-exp racket
(require redex/reduction-semantics)
(require "../steps/relAcqNaRlxPost.rkt")
(require "testTerms.rkt")
(require "../core/parser.rkt")

; (require redex/gui)
; (traces step testMP+read+rlx)

(test-->>∃ step testMP+read+rlx
           'stuck)

(test-->>∃ step testMP+read+rel
           'stuck)