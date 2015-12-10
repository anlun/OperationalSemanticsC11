#lang racket
(require parser-tools/lex
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc)
(provide parse)

(define-tokens       a (NUM VAR LOC
                        MM))
(define-empty-tokens b (+ - * == !=
                        CHOICE
                        PROJ1 PROJ2
                        POPEN PCLOSE
                        BOPEN BCLOSE
                        IF THEN ELSE
                        REPEAT REPEATFUEL END
                        SPW TOPEN TSEP TCLOSE
                        COMMA SEMICOLON
                        UNDERSCORE ASSIGN CAS
                        RET STUCK
                        EOF))
(define-lex-trans number
  (syntax-rules ()
    ((_ digit)
     (re-: (re-? (re-or "-" "+")) (uinteger digit)
           (re-? (re-: "." (re-? (uinteger digit))))))))
(define-lex-trans uinteger
  (syntax-rules ()
    ((_ digit) (re-+ digit))))
(define-lex-abbrevs
  (digit10 (char-range "0" "9"))
  (number10 (number digit10))
  (identifier-characters (re-or (char-range "A" "Z")
                                (char-range "a" "z")
                                digit10))
  (identifier (re-+ identifier-characters)))

(define lang-lexer
  (lexer
   ("-"      (token--))
   ("+"      (token-+))
   ("*"      (token-*))
   ("=="     (token-==))
   ("!="     (token-!=))
   ("choice" (token-CHOICE))
   ("_1"     (token-PROJ1))
   ("_2"     (token-PROJ2))
   ("("      (token-POPEN))
   (")"      (token-PCLOSE))
   ("["      (token-BOPEN))
   ("]"      (token-BCLOSE))
   
   ("ret"    (token-RET))
   ("stuck"  (token-STUCK))
   ("_"      (token-UNDERSCORE))
   (":="     (token-ASSIGN))
   ("cas_"   (token-CAS))
   (","      (token-COMMA))
   (";"      (token-SEMICOLON))
   ("if"     (token-IF))
   ("then"   (token-THEN))
   ("else"   (token-ELSE))
   ("repeat" (token-REPEAT))
   ("end"    (token-END))
   ("repeatFuel" (token-REPEATFUEL))
   
   ("spw"    (token-SPW))
   ("{{{"    (token-TOPEN))
   ("\\\\\\" (token-TSEP))
   ("}}}"    (token-TCLOSE))

   ((re-or "sc" "relAcq" "acq" "rel" "rlx" "na") (token-MM (string->symbol lexeme)))

   ((re-+ number10)       (token-NUM (string->number lexeme)))
   ((re-: "r" identifier) (token-VAR (string->symbol lexeme)))

   (identifier            (token-LOC lexeme))
   ;; recursively calls the lexer which effectively skips whitespace
   (whitespace (lang-lexer input-port))
   ((eof) (token-EOF))))

(define lang-parser
  (parser
   (start stmt)
   (end EOF)
   (error void)
   (tokens a b)
   (precs (left == !=) (left - +) (left *) (right SEMICOLON))
   (grammar
    (locvar ((LOC) $1)
            ((VAR) $1))
    (stmt ((RET exp) (list 'ret $2))
          ((STUCK)   'stuck)
          ((VAR ASSIGN stmt SEMICOLON stmt) (list $3 '>>= (list 'λ $1 $5)))
          ((stmt SEMICOLON stmt)            (list $1 '>>= (list 'λ 'r-1 $3)))
          ((locvar UNDERSCORE MM ASSIGN exp) (list 'write $3 $1 $5))
          ((locvar UNDERSCORE MM)            (list 'read  $3 $1))
          ((CAS MM UNDERSCORE MM
                POPEN
                locvar COMMA exp COMMA exp
                PCLOSE)
           (list 'cas  $2 $4 $6 $8 $10))
          ((IF exp THEN stmt ELSE stmt) (list 'if $2 $4 $6))
          ((REPEAT stmt END)            (list 'repeat $2))
          ((REPEATFUEL NUM stmt END)    (list 'repeatFuel $2 $3))
          ((SPW TOPEN stmt TSEP stmt TCLOSE)
           (list 'spw $3 $5)))
    (exp  ((NUM) $1)
          ((locvar) $1)
          ((exp +  exp) (list '+ $1 $3))
          ((exp -  exp) (list '- $1 $3))
          ((exp *  exp) (list '* $1 $3))
          ((exp == exp) (list '== $1 $3))
          ((exp != exp) (list '!= $1 $3))
          ((exp  PROJ1) (list 'proj1 $1))
          ((exp  PROJ2) (list 'proj2 $1))
          ((CHOICE exp exp) (list 'choice $2 $3))
          ((BOPEN exp exp BCLOSE) (list $2 $3))
          ((POPEN exp PCLOSE) $2)))))

(define (lex-this lexer input) (lambda () (lexer input)))

(define (parse input)
  (lang-parser (lex-this lang-lexer (open-input-string input))))
