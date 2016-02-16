#lang racket

(require "util.rkt" "ast.rkt" "debug.rkt" "parse.rkt")
(provide source-info parse-port parse-string parse-file)

(require parser-tools/lex parser-tools/yacc)
(require (prefix-in : parser-tools/lex-sre))

;; ========== TOKENS ==========
(define-tokens datafun-tokens (number string id Id))
(define-empty-tokens datafun-empty-tokens
  (eof
   ;; punctuation
   LP RP LSQUARE RSQUARE LCURLY RCURLY
   COMMA BAR : SEMI _
   = <= < >= >
   -> ~> ->- ->+ =>
   + * - / ++
   ∨ ∈ ⋁
   ;; declarations
   TYPE FUN VAL CONST MONO ANTI
   ;; types
   SET MAP
   ;; expressions
   LAMBDA LET FIX CASE IF THEN ELSE WHEN UNLESS
   IN IN? FOR LUB
   TRUE FALSE EMPTY))


;; ========== LEXER ==========
(define datafun-lex
  (lexer-src-pos
   ;; whitespace & comments
   [(:+ whitespace) (return-without-pos (datafun-lex input-port))]
   ;; we don't support nested comments yet, alas.
   [(:: "(*" (complement (:: any-string "*)" any-string)) "*)")
     (return-without-pos (datafun-lex input-port))]

   ;; literals
   [(:+ numeric) (token-number (string->number lexeme))]
   [(:: "\"" (:* (:or (:~ "\"") (:: "\\" any-char))) "\"")
    (token-string (with-input-from-string lexeme read))]

   ;; punctuation and symbols
   ["(" 'LP]      [")" 'RP]
   ["{" 'LCURLY]  ["}" 'RCURLY]
   ["[" 'LSQUARE] ["]" 'RSQUARE]
   ["," 'COMMA] ["|" 'BAR] [":" ':] [";" 'SEMI] ["_" '_]
   ["=" '=] ["<=" '<=] ["<" '<] [">=" '>=] [">" '>]
   ["=>" '=>] ["->" '->] ["~>"  '~>] ["->+" '->+] ["->-" '->-]
   ["+" '+] ["-" '-] ["*" '*] ["/" '/]
   ["∨" '∨] ["⋁" '⋁] ["∈" '∈]

   ;; declaration keywords
   ["type" 'TYPE]   ["val" 'VAL]   ["fun" 'FUN]
   ["const" 'CONST] ["mono" 'MONO] ["anti" 'ANTI]

   ;; type keywords
   ["set" 'SET] ["map" 'MAP]

   ;; expression keywords
   [(:or "fn" "λ") 'LAMBDA] ["let" 'LET] ["fix" 'FIX] ["in" 'IN] ["case" 'CASE]
   ["if" 'IF] ["then" 'THEN] ["else" 'ELSE]
   ["when" 'WHEN] ["unless" 'UNLESS]
   ["for"   'FOR]
   [(:or "in?" "∈?") 'IN?]
   [(:or "empty" "ε") 'EMPTY]
   ["lub"   'LUB]
   ["true"  'TRUE] ["false" 'FALSE]

   ;; identifiers. this must come last so that we prefer to lex things as
   ;; keywords than as identifiers.
   [(:: (:& alphabetic lower-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-id (string->symbol lexeme))]
   [(:: (:& alphabetic upper-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-Id (string->symbol lexeme))]))


;; ========== GRAMMAR / PARSER ==========

;; bind source-info to a mutable hasheq (a weak hasheq is advisable, but not
;; mandatory) if you want parsing to annotate the expressions/decls/etc it
;; parses with source position info.
;;
;; it will bind each expression, pat, and decl to (list start-pos end-pos),
;; where start-pos & end-pos are position structures.
(define source-info (make-parameter (make-weak-hasheq)))
(define (annotate! obj start-pos end-pos)
  (when (source-info)
    (hash-set! (source-info) obj (list start-pos end-pos)))
  obj)

(define/match (parse-func how)
  [('expr)  expr-parse]
  [('type)  type-parse]
  [('pat)   pat-parse]
  [('decl)  decl-parse]
  [('decls) decls-parse])

;; this has hella shift-reduce conflicts, but I don't care.
(match-define (list decls-parse decl-parse type-parse pat-parse expr-parse)
  (parser
   (start decls decl type pat expr)
   (src-pos)
   (tokens datafun-tokens datafun-empty-tokens)
   ;; TODO: more useful error handling / error messages
   (error (lambda (tok-ok? tok-name tok-value start-pos end-pos)
            (error "parse error:" tok-ok? tok-name tok-value
                   start-pos end-pos)))
   (end eof)
   ;; for now, just for testing/bootstrapping, our semantic actions generate
   ;; s-expressions that parse.rkt can parse.
   (grammar

    ;; names - like identifiers, but allowing binding of infix operators.
    (name ((id) $1) ((LP oper RP) $2))
    (names (() '()) ((name names) (cons $1 $2)))
    (names1 ((name names) (cons $1 $2)))
    (name-list1
     ((name) `(,$1))
     ((name COMMA name-list1) (cons $1 $3)))

    ;; ----- decls -----
    (decls
     (() '())
     ((decl decls) (append $1 $2)))
    (decl ((d) (annotate! $1 $1-start-pos $1-end-pos)))
    (d
     ((TYPE name = type)            `((type ,$2 = ,$4)))
     ((tone? VAL name-list1 : type) `((,@$1 ,@$3 : ,$5)))
     ;; gah. this is conflicting with the previous rule somehow.
     ;; for example, (parse "val x : nat" #:as 'decls) errors.
     ;((tone? VAL name : type = expr) `((,@$1 ,$3 : ,$5) (,$3 = ,$7)))
     ((tone? VAL name = expr)       `((,@$1 ,$3 = ,$5)))
     ((tone? FIX name = expr)       `((,@$1 fix ,$3 = ,$5)))
     ((tone? FUN name names1 = expr)            `((,@$1 ,$3 ,@$4 = ,$6)))
     ((tone? FUN LP name oper name RP = expr)   `((,@$1 ,$5 ,$4 ,$6 = ,$9))))

    (tone? (() '()) ((tone) (list $1)))
    (tone ((CONST) 'const) ((MONO) 'mono) ((ANTI) 'anti))

    ;; ----- types -----
    ;; TODO: record types
    (type ((t) (annotate! $1 $1-start-pos $1-end-pos)))
    (t
     ((t-func) $1)
     ((t-sum)  `(+ ,@$1)))
    (t-func
     ((t-arg) $1)
     ((t-arg -> t-func) `(,$1 -> ,$3))
     ((t-arg ~> t-func) `(,$1 ~> ,$3))
     ((t-arg ->+ t-func) `(,$1 ->+ ,$3))
     ((t-arg ->- t-func) `(,$1 ->- ,$3)))
    (t-arg
     ((t-product) (match $1
                    [(list x) x]
                    [xs `(* ,@xs)])))
    (t-product
     ((t-factor)              (list $1))
     ((t-factor * t-product)  (cons $1 $3)))
    (t-factor
     ((t-atom)                      $1)
     ((SET t-atom)                  `(set ,$2))
     ((MAP t-atom t-atom)           `(map ,$2 ,$3))
     ((LCURLY type RCURLY)          `(set ,$2))
     ((LCURLY t-list+ RCURLY)       `(set (* ,@$2)))
     ((LCURLY type : type RCURLY)   `(map ,$2 ,$4)))
    (t-atom
     ((id)          $1)
     ((LP RP)       '(*))
     ((LP type RP)  $2))
    (t-sum
     ((t-ctor)           (list $1))
     ((t-ctor BAR t-sum) (cons $1 $3)))
    (t-ctor
     ((Id) $1)
     ((Id LP t-list RP) `(,$1 ,@$3)))
    (t-list
     (()                        '())
     ((type)                    `(,$1))
     ((type COMMA t-list)  (cons $1 $3)))
    (t-list+
     ((type COMMA t-list) (cons $1 $3)))

    ;; ----- literals -----
    (lit ((number)      $1)
         ((string)      $1)
         ((TRUE)        '#t)
         ((FALSE)       '#f))

    ;; ----- patterns -----
    (pat ((p) (annotate! $1 $1-start-pos $1-end-pos)))
    (p
     ((name)            $1)
     ((lit)             $1)
     ((_)               '_)
     ((= expr)          `(= ,$2))
     ((LP pat RP)       $2)
     ((LP p-list* RP)   `(cons ,@$2))
     ((Id)              `',$1)
     ((Id LP p-list RP) (match $3
                          ['()  `',$1]
                          [pats `(',$1 ,@pats)])))
    (p-list* (() '())
             ((pat COMMA p-list) (cons $1 $3)))
    (p-list ((p-list*) $1)
            ((pat)         (list $1)))

    ;; ----- expressions -----
    (expr ((e) (annotate! $1 $1-start-pos $1-end-pos)))
    (e
     ((LAMBDA names => expr)        `(fn ,@$2 ,$4))
     ((LET decls IN expr)           `(let ,$2 ,$4))
     ((CASE e-op cases)             `(case ,$2 ,@$3))
     ((IF e-op THEN e-op ELSE e-op) `(if ,$2 ,$4 ,$6))
     ((WHEN e-op THEN expr)         `(when ,$2 ,$4))
     ((UNLESS e-op THEN expr)       `(unless ,$2 ,$4))
     ((FIX name = expr)             `(fix ,$2 ,$4))
     ((FIX name : type = expr)      `(as ,$4 (fix ,$2 ,$6)))
     ((⋁ LP loops RP expr)          `(,@$3 lub ,$5))
     ((FOR LP loops RP expr)        `(,@$3 lub ,$5))
     ((e-asc)                       $1))
    (e-asc
     ((e-asc : type)    `(as ,$3 ,$1))
     ((e-op)            $1))
    (e-op
     ;; for now, everything is left associative. TODO: precedence parsing.
     ((e-op oper e-app)      `(,$2 ,$1 ,$3))
     ((e-op IN? e-app)       `(,$1 in? ,$3))
     ((Id LP e-list RP)      `(',$1 ,@$3))
     ((Id)                   `',$1)
     ((e-app)                $1))
    (e-app
     ((e-app e-atom)   `(,$1 ,$2))
     ((e-atom)         $1))
    (e-atom
     ((name)                            $1)
     ((lit)                             $1)
     ((EMPTY)                           'empty)
     ((LP expr RP)                      $2)
     ((LP expr BAR loops RP)            `(,$2 ,@$4))
     ((LP e-list* RP)                   `(cons ,@$2))
     ((LCURLY e-list RCURLY)            `(set ,@$2))
     ((LCURLY e-op BAR loops RCURLY)    `((set ,$2) ,@$4))
     ;; TODO: multiple-element map literals; map comprehensions?
     ((LCURLY : RCURLY)                 `(map))
     ((LCURLY e-kv-list1 RCURLY)        `(map ,@$2)))

    (oper ((=) '=) ((<=) '<=) ((>=) '>=) ((<) '<) ((>) '>)
          ((++) '++) ((+) '+) ((-) '-) ((*) '*) ((/) '/)
          ((∨) 'lub) ((LUB) 'lub))

    (e-kv ((e-op : e-op) (list $1 $3)))
    (e-kv-list1
     ((e-kv)                  (list $1))
     ((e-kv COMMA e-kv-list1) (cons $1 $3)))

    (e-list
     ((e-list*) $1)
     ((e-op) (list $1)))
    (e-list*
     (() '())
     ((e-op COMMA e-list) (cons $1 $3)))

    (cases
     (() '())
     ((case cases) (cons $1 $2)))
    (case  ((BAR pat => expr) (list $2 $4)))

    (loops
     ((loop) $1)
     ((loop COMMA loops) (append $1 $3)))
    ;; TODO: looping across a map.
    (loop
     ((e-op)         `(when ,$1))
     ((pat IN e-op)  `(for ,$1 in ,$3))
     ((pat ∈ e-op)   `(for ,$1 in ,$3))))))

(define (parse-port port #:as how)
  (define func (parse-func how))
  (source-info (make-weak-hasheq))
  (func (lambda () (datafun-lex port))))

(define (parse-string s #:as [how 'expr])
  (define p (open-input-string s))
  (port-count-lines! p)
  (parse-port p #:as how))

(define (parse-file filename #:as [how 'decls])
  (call-with-input-file filename
    (lambda (port)
      (port-count-lines! port)
      (parse-port port #:as how))))


;; TESTING
;; (define parse parse-string)

;; (define (tokenize s)
;;   (define port (open-input-string s))
;;   (define (gen) (datafun-lex port))
;;   (generate/list
;;    (let loop ()
;;      (define tok (gen))
;;      (unless (eq? 'eof (position-token-token tok))
;;        (yield tok)
;;        (loop)))))

;; (require "repl.rkt")
;; (define decls (void))
;; (define defns (void))
;; (define (test)
;;   (set! decls (parse-file "ml-example.df"))
;;   (set! defns (parse-decls decls))
;;   (eval-defns! defns))
