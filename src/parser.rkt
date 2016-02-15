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
   TYPE FUN VAL
   ;; types
   * + SET MAP
   ;; patterns
   WILD
   ;; expressions
   LAMBDA LET FIX CASE IF THEN ELSE WHEN UNLESS
   IN ∈ FOR IN?
   TRUE FALSE EMPTY))


;; ========== LEXER ==========
(define datafun-lex
  (lexer-src-pos
   ;; whitespace & comments
   [(:+ whitespace) (return-without-pos (datafun-lex input-port))]
   ;; we don't support nested comments yet, alas.
   [(:: "(*" (complement (:: any-string "*)" any-string)) "*)")
     (return-without-pos (datafun-lex input-port))]

   ;; punctuation
   ["(" 'LPAREN]  [")" 'RPAREN] ["{" 'LCURLY]  ["}" 'RCURLY]
   ["[" 'LSQUARE] ["]" 'RSQUARE]
   ["=>" '=>] ["," 'COMMA] ["|" 'BAR] [":" ':] [";" 'SEMI] ["=" '=]

   ;; declarations
   ["type" 'TYPE] ["val" 'VAL] ["fun" 'FUN]
   ["const" (token-tone 'any)]
   ["mono"  (token-tone 'mono)]
   ["anti"  (token-tone 'anti)]

   ;; types
   ["*" '*] ["+" '+] ["set" 'SET] ["map" 'MAP]
   ["->"              (token-arrow 'any)]
   [(:or "~>" "->+")  (token-arrow 'mono)]
   ["->-"             (token-arrow 'anti)]

   ;; patterns
   ["_" 'WILD]

   ;; expressions
   [(:or "fn" "λ") 'LAMBDA] ["let" 'LET] ["fix" 'FIX] ["in" 'IN] ["case" 'CASE]
   ["if" 'IF] ["then" 'THEN] ["else" 'ELSE]
   ["when" 'WHEN] ["unless" 'UNLESS]
   [(:or "-" "<=" "<" ">=" ">") (token-binop (string->symbol lexeme))]
   ;; ideally IN? would be a token-binop, but parse.rkt handles 'in? with infix
   ;; notation instead of prefix.
   [(:or "in?" "∈?") 'IN?]
   [(:or "∨" "lub")  (token-binop 'lub)]
   [(:or "empty" "ε") 'EMPTY]
   [(:or "for" "⋁")   'FOR]
   ["∈" '∈]

   ;; literals.
   ["true" 'TRUE] ["false" 'FALSE]
   [(:+ numeric) (token-number (string->number lexeme))]
   [(:: "\"" (:* (:or (:~ "\"") (:: "\\" any-char))) "\"")
    (token-string (with-input-from-string lexeme read))]

   ;; identifiers
   [(:: (:& alphabetic lower-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-id (string->symbol lexeme))]
   [(:: (:& alphabetic upper-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-Id (string->symbol lexeme))]))


;; ========== GRAMMAR / PARSER ==========

;; this has hella shift-reduce conflicts, but I don't care.
(match-define (list datafun-parse-decls datafun-parse-decl
                    datafun-parse-type datafun-parse-pat datafun-parse-expr)
  (parser
   (start decls decl type pat expr)
   (src-pos)
   (tokens datafun-tokens datafun-empty-tokens)
   ;; FIXME: error handling.
   (error (lambda (tok-ok? tok-name tok-value start-pos end-pos)
            (error "parse error:" tok-ok? tok-name tok-value
                   start-pos end-pos)))
   (end eof)
   ;; for now, just for testing/bootstrapping, our semantic actions generate
   ;; s-expressions that parse.rkt can parse.
   (grammar

    (decls (() '())
           ((decl decls) (append $1 $2)))
    (decl ((TYPE id = type)             `((type ,$2 = ,$4)))
          ((tone? VAL comma-ids1 : type) `((,@$1 ,@$3 : ,$5)))
          ;; gah. this is conflicting with the previous rule somehow.
          ;; for example, (parse "val x : nat" #:as 'decls) errors.
          ;((tone? VAL id : type = expr) `((,@$1 ,$3 : ,$5) (,$3 = ,$7)))
          ((tone? VAL id = expr)        `((,@$1 ,$3 = ,$5)))
          ((tone? FIX id = expr)        `((,@$1 fix ,$3 = ,$5)))
          ((tone? FUN id args = expr)   `((,@$1 ,$3 ,@$4 = ,$6))))
    (args (() '())
          ((id args) (cons $1 $2)))
    (comma-ids1 ((id) `(,$1))
                ((id COMMA comma-ids1) (cons $1 $3)))

    (tone? (()     '())
           ((tone) (list $1)))

    ;; TODO: record types
    (type ((func-type) $1))
    (func-type ((arg-type) $1)
               ((arg-type arrow func-type)
                (let ([arrow (match $2 ['any '->] ['mono '~>] ['anti '->-])])
                  `(,$1 ,arrow ,$3))))
    (arg-type ((factor-types) (match $1 [(list x) x] [xs `(* ,@xs)])))
    (factor-types ((factor-type * factor-types) (cons $1 $3))
                  ((factor-type) (list $1)))
    (factor-type
     ((atom-type)               $1)
     ((summand-types1)          (cons '+ $1))
     ((SET atom-type)           `(set ,$2))
     ((MAP atom-type atom-type) `(map ,$2 ,$3)))
    (atom-type
     ((id)                     $1)
     ((LPAREN RPAREN)          '(*))
     ((LPAREN type RPAREN)     $2))
    (summand-types1
     ((summand-type)                    (list $1))
     ((summand-type + summand-types1)   (cons $1 $3)))
    (summand-type ((Id) $1)
                  ((Id LPAREN comma-types RPAREN) `(,$1 ,@$3)))
    (comma-types (()                        '())
                 ((type)                    `(,$1))
                 ((type COMMA comma-types)  (cons $1 $3)))

    ;; literals
    (lit ((number)      $1)
         ((string)      $1)
         ((TRUE)        '#t)
         ((FALSE)       '#f))

    ;; patterns
    (pat  ((id)                         $1)
          ((lit)                        $1)
          ((WILD)                       '_)
          ((= expr)                     `(= ,$2))
          ((LPAREN pat RPAREN)          $2)
          ((LPAREN comma-pats* RPAREN)  `(cons ,@$2))
          ((Id)                         `',$1)
          ((Id LPAREN comma-pats RPAREN)    (match $3
                                              ['()  `',$1]
                                              [pats `(',$1 ,@pats)])))
    (comma-pats* (() '())
                 ((pat COMMA comma-pats) (cons $1 $3)))
    (comma-pats ((comma-pats*) $1)
                ((pat)         (list $1)))

    ;; expressions
    (expr ((LAMBDA args => expr)        `(fn ,@$2 ,$4))
          ((LET decls IN expr)          `(let ,$2 ,$4))
          ((CASE op-expr cases)         `(case ,$2 ,@$3))
          ((IF op-expr THEN op-expr ELSE op-expr)    `(if ,$2 ,$4 ,$6))
          ((WHEN op-expr THEN expr)     `(when ,$2 ,$4))
          ((UNLESS op-expr THEN expr)   `(unless ,$2 ,$4))
          ((FIX id = expr)              `(fix ,$2 ,$4))
          ((FIX id : type = expr)       `(as ,$4 (fix ,$2 ,$6)))
          ((FOR LPAREN loops RPAREN expr) `(,@$3 lub ,$5))
          ((asc-expr)                    $1))
    (asc-expr ((asc-expr : type)    `(as ,$3 ,$1))
              ((op-expr)            $1))
    (op-expr
     ;; for now, everything is left associative. TODO: precedence parsing.
     ((op-expr oper app-expr)      `(,$2 ,$1 ,$3))
     ((op-expr IN? app-expr)       `(,$1 in? ,$3))
     ((Id LPAREN comma-exprs RPAREN) `(',$1 ,@$3))
     ((Id)                          `',$1)
     ((app-expr)                    $1))
    (oper ((binop) $1) ((=) '=) ((+) '+) ((*) '*))
    (app-expr
     ((app-expr arg-expr)   `(,$1 ,$2))
     ((arg-expr)            $1))
    (arg-expr
     ((id)                              $1)
     ((lit)                             $1)
     ((EMPTY)                           'empty)
     ((LPAREN expr RPAREN)              $2)
     ((LPAREN comma-exprs* RPAREN)      `(cons ,@$2))
     ((LCURLY comma-exprs RCURLY)       `(set ,@$2))
     ((LCURLY op-expr BAR loops RCURLY) `((set ,$2) ,@$4))
     ;; TODO: multiple-element map literals; map comprehensions?
     ((LCURLY : RCURLY)                 `(map))
     ((LCURLY kv-exprs1 RCURLY)         `(map ,@$2)))

    (kv-exprs1 ((kv-expr) (list $1))
               ((kv-expr COMMA kv-exprs1) (cons $1 $3)))
    (kv-expr   ((op-expr : op-expr) (list $1 $3)))

    (comma-exprs ((comma-exprs*) $1)
                 ((op-expr) (list $1)))
    (comma-exprs* (() '())
                  ((op-expr COMMA comma-exprs) (cons $1 $3)))

    (cases (() '())
           ((case cases) (cons $1 $2)))
    (case  ((BAR pat => expr) (list $2 $4)))
    (loops ((loop) $1)
           ((loop COMMA loops) (append $1 $3)))
    ;; TODO: looping across a map.
    (loop  ((op-expr)         `(when ,$1))
           ((pat IN op-expr)  `(for ,$1 in ,$3))
           ((pat ∈ op-expr)   `(for ,$1 in ,$3)))

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

(define/match (parse-func how)
  [('expr)  datafun-parse-expr]
  [('type)  datafun-parse-type]
  [('pat)   datafun-parse-pat]
  [('decl)  datafun-parse-decl]
  [('decls) datafun-parse-decls])

(define (parse s #:as [how 'expr])
  (define port (open-input-string s))
  ((parse-func how) (lambda () (datafun-lex port))))

(define (parse-file filename #:as [how 'decls])
  (call-with-input-file filename
    (lambda (p)
      (port-count-lines! p)
      ((parse-func how) (lambda () (datafun-lex p))))))


;; TESTING
;; (require "repl.rkt")
;; (define decls (parse-file "ml-example.df"))
;; (define defns (parse-decls decls))
