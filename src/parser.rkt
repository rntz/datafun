#lang racket

(require "util.rkt" "ast.rkt" "debug.rkt" "parse.rkt")
(provide (all-defined-out))

(require parser-tools/lex parser-tools/yacc)
(require (prefix-in : parser-tools/lex-sre))

;; ========== TOKENS ==========
(define-tokens datafun-tokens
  (;; types
   arrow
   ;; declarations
   tone
   ;; expressions
   number string binop
   ;; identifiers
   id Id))

(define-empty-tokens datafun-empty-tokens
  (eof
   ;; punctuation
   LPAREN RPAREN LSQUARE RSQUARE LCURLY RCURLY
   COMMA BAR : SEMI = =>
   ;; declarations
   TYPE
   ;; types
   * + SET MAP
   ;; patterns
   WILD
   ;; expressions
   LAMBDA LET FIX IN CASE IF THEN ELSE
   TRUE FALSE UNIT))

;; TODO: lub-comprehensions


;; ========== LEXER ==========
(define datafun-lex
  (lexer-src-pos
   ;; punctuation
   ["(" 'LPAREN]  [")" 'RPAREN] ["{" 'LCURLY]  ["}" 'RCURLY]
   ["[" 'LSQUARE] ["]" 'RSQUARE]
   ["=>" '=>] ["," 'COMMA] ["|" 'BAR] [":" ':] [";" 'SEMI] ["=" '=]

   ;; declarations
   ["type" 'TYPE]
   ["const" (token-tone 'any)]
   ["mono"  (token-tone 'mono)]
   ["anti"  (token-tone 'anti)]

   ;; types
   ["*" '*] ["+" '+] ["Set" 'SET] ["Map" 'MAP]
   ["->"              (token-arrow 'any)]
   [(:or "~>" "->+")  (token-arrow 'mono)]
   ["->-"             (token-arrow 'anti)]

   ;; patterns
   ["_" 'WILD]

   ;; expressions
   [(:or "fn" "λ") 'LAMBDA] ["let" 'LET] ["fix" 'FIX] ["in" 'IN] ["case" 'CASE]
   ["if" 'IF] ["then" 'THEN] ["else" 'ELSE]
   [(:or "in?" "<=" "<" ">=" ">") (token-binop (string->symbol lexeme))]
   [(:or "∨" "lub") (token-binop 'lub)]
   [(:or "empty" "ε") 'UNIT]
   ;; literals
   ["true" 'TRUE] ["false" 'FALSE]
   [(:+ numeric) (token-number (string->number lexeme))]
   ;; TODO: string literals

   ;; identifiers
   [(:: (:& alphabetic lower-case)
        (:* (:or alphabetic numeric (char-set "-_"))))
    (token-id (string->symbol lexeme))]
   [(:: (:& alphabetic upper-case)
        (:* (:or alphabetic numeric (char-set "-_"))))
    (token-Id (string->symbol lexeme))]

   ;; whitespace & comments
   [(:+ whitespace) (return-without-pos (datafun-lex input-port))]))


;; ========== GRAMMAR / PARSER ==========

;; this has hella shift-reduce conflicts, but I don't care.
(match-define (list datafun-parse-decl datafun-parse-type datafun-parse-pat
                    datafun-parse-expr)
  (parser
   (start decl type pat expr)
   (src-pos)
   (tokens datafun-tokens datafun-empty-tokens)
   ;; FIXME: error handling.
   (error (lambda _ (error "fuck")))
   (end eof)
   ;; for now, just for testing/bootstrapping, our semantic actions generate
   ;; s-expressions that parse.rkt can parse.
   (grammar

    (decl ((TYPE id = type) (list `(type ,$2 ,$4)))
          ((id : type)      (list `(: ,$1 ,$3)))
          ((id args = expr) (list `(= ,$1 ,$2 ,$4))))
    (args (() '())
          ((id args) (cons $1 $2)))

    ;; TODO: sum/variant types, record types
    (type ((func-type) $1))
    (func-type ((arg-type) $1)
               ((arg-type arrow func-type)
                (let ([arrow (match $2 ['any '->] ['mono '~>] ['anti '->-])])
                  `(,$1 ,arrow ,$3))))
    (arg-type ((factor-types) (match $1 [(list x) x] [xs `(* ,@xs)])))
    (factor-types ((factor-type * factor-types) (cons $1 $3))
                  ((factor-type) (list $1)))
    (factor-type
     ((id)                     $1)
     ((LPAREN type RPAREN)     $2)
     ((SET type)               `(set ,$2))
     ((MAP type type)          `(map ,$2 ,$3)))

    ;; literals
    (lit ((number)      $1)
         ((TRUE)        '#t)
         ((FALSE)       '#f))

    ;; patterns
    (pat  ((id)                         $1)
          ((lit)                        $1)
          ((WILD)                       '_)
          ((= expr)                     `(= ,$2))
          ((LPAREN pat RPAREN)          $2)
          ((LPAREN comma-pats RPAREN)   `(cons ,@$2))
          ((Id LPAREN comma-pats RPAREN)    (match $3
                                              ['()  `',$1]
                                              [pats `(',$1 ,@pats)]))
          ((Id)                             `',$1))
    (comma-pats (() '())
                ((pat) (list $1))
                ((pat COMMA comma-pats) (cons $1 $3)))

    ;; expressions
    (expr ((LPAREN expr RPAREN) $2)
          ((LPAREN comma-exprs RPAREN) `(cons ,@$2))
          ((id)                 $1)
          ((lit)                $1)
          ((UNIT)               'empty)
          ((expr binop expr)    `(,$2 ,$1 ,$3)) ;woo prefix notation
          ((expr * expr)        `(* ,$1 ,$3))
          ((expr + expr)        `(+ ,$1 ,$3))
          ((expr = expr)        `(= ,$1 ,$3))
          ((expr : type)        `(as ,$3 ,$1))
          ;; TODO: let-expressions
          ((LAMBDA args => expr)            `(fn ,@$2 ,$4))
          ((IF expr THEN expr ELSE expr)    `(if ,$2 ,$4 ,$6))
          ((CASE expr cases)                `(case ,$2 ,@$3))
          ((FIX id = expr)                  `(fix ,$2 ,$4))
          ((FIX id : type = expr)           `(as ,$4 (fix ,$2 ,$6)))
          ((LCURLY comma-exprs RCURLY)      `(set ,@$2))
          ((LCURLY expr BAR loops RCURLY)   `((set ,$2) ,@$4)))
    (comma-exprs (() '())
                 ((expr) (list $1))
                 ((expr COMMA comma-exprs) (cons $1 $3)))
    (cases (() '())
           ((case cases) (cons $1 $2)))
    (case  ((BAR pat => expr) (list $2 $4)))
    (loops ((loop) $1)
           ((loop COMMA loops) (append $1 $3)))
    ;; TODO: looping across a map.
    (loop  ((expr)         `(when ,$1))
           ((expr IN expr) `(for ,$1 in ,$3)))

    )))

(define (tokenize s)
  (define port (open-input-string s))
  (define (gen) (datafun-lex port))
  (generate/list
   (let loop ()
     (define tok (gen))
     (unless (eq? 'eof (position-token-token tok))
       (yield tok)
       (loop)))))

(define (parse s #:as [how 'expr])
  (define port (open-input-string s))
  ((match how
     ['expr datafun-parse-expr]
     ['type datafun-parse-type]
     ['pat  datafun-parse-pat]
     ['decl datafun-parse-decl])
   (lambda () (datafun-lex port))))
