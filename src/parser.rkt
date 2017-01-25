#lang racket

(provide parse-port parse-string parse-file)

(require "util.rkt" "ast.rkt" "defns.rkt" "source-info.rkt" "lex.rkt")
(require parser-tools/lex parser-tools/yacc)

;; ========== Parameters ==========
(define current-source-name (make-parameter #f))


;; ========== Public functions ==========
(define (parse-port port
                    #:as how
                    #:source-name [source-name #f])
  (parameterize ([current-source-name source-name])
   ((parser-for how) (lambda () (datafun-lex port)))))

(define (parse-string s
                      #:as [how 'expr]
                      #:source-name [source-name "<string>"])
  (define port (open-input-string s))
  (port-count-lines! port)
  (parse-port port #:as how #:source-name source-name))

(define (parse-file filename
                    #:as [how 'decls]
                    #:source-name [source-name filename])
  (call-with-input-file filename
    (lambda (port)
      (port-count-lines! port)
      (parse-port port #:as how #:source-name source-name))))

;; Helper
(define/match (parser-for how)
  [('expr)  expr-parse]
  [('type)  type-parse]
  [('pat)   pat-parse]
  [('decls) decls-parse]
  [('decls-or-expr) decls-or-expr-parse]
  [((? procedure?)) how])


;; ========== GRAMMAR / PARSER ==========

;; TODO: more useful error handling / error messages
;; TODO: print out positions better
(define (parse-error tok-ok? tok-name tok-value start-pos end-pos)
  (match* (tok-ok? tok-value)
    [(#t #f) (error (format "unexpected token ~a (~v, ~v)"
                            tok-name start-pos end-pos))]
    [(#t _)  (error (format "unexpected '~a' token: ~s (~v, ~v)"
                            tok-name tok-value start-pos end-pos))]
    ;; this shouldn't happen; indicates a mismatch b/w our lexer & our parser.
    ;; real unrecognized tokens will make the lexer throw an error.
    [(#f _) (error (format "invalid token (~v, ~v)" start-pos end-pos))]))

;; this still has some shift-reduce conflicts, but I don't care.
(match-define (list decls-parse type-parse pat-parse expr-parse
                    decls-or-expr-parse)
  (parser
   (start decls type pat expr decls-or-expr)
   (src-pos)
   (tokens datafun-tokens datafun-empty-tokens)
   (error parse-error)
   (end eof)

   (grammar
    (decls-or-expr
     ((decls) `(decls ,$1))
     ((expr)  `(expr ,$1)))

    ;; names - like identifiers, but allowing binding of infix operators.
    (name ((id) $1) ((LP oper RP) $2))
    (names (() '()) ((name names) (cons $1 $2)))
    (names1 ((name names) (cons $1 $2)))
    (name-list1
     ((name) `(,$1))
     ((name COMMA name-list1) (cons $1 $3)))

    (oper ((=) '=) ((<=) '<=) ((>=) '>=) ((<) '<) ((>) '>)
          ((++) '++) ((+) '+) ((-) '-) ((*) '*) ((/) '/)
          ((**) 'cross) ((×) 'cross)
          ((•) 'compose))

    ;; some simple synonyms
    (is ((IS) (void)) ((=)  (void)))

    ;; ----- decls -----
    (decls
     (() '())
     ((decl decls) (append $1 $2)))
    (decl
     ;; TODO: refactor this mess
     ;; TODO: (VAL pat = expr)?
     ((TYPE name = type)            (list (decl-type $2 $4)))
     ((VAL name-list1 : type)       (for/list ([n $2]) (decl-val-type n $4)))
     ((tone name-list1)             (for/list ([n $2]) (decl-val-tone n $1)))
     ((tone name-list1 : type)      (let*/list ([n $2])
                                      (list (decl-val-type n $4)
                                            (decl-val-tone n $1))))
     ((tone VAL name = expr)        (list (decl-val-tone $3 $1)
                                          (decl-val $3 $5)))
     ((VAL name = expr)             (list (decl-val $2 $4)))
     ((FIX name = e-bars)           (list (decl-val $2 (e-fix $2 $4))))
     ((FUN name names1 = expr)      (list (decl-val $2 (e-lam* $3 $5))))
     ((FUN LP name oper name RP = expr)
      (list (decl-val $4 (e-lam $3 (e-lam $5 $8))))))

    ;; TODO: (REL ...) declarations!

    (tone? (() '()) ((tone) (list $1)))
    (tone ((DISC) 'disc) ((MONO) 'mono) ((ANTI) 'anti))

    ;; ----- types -----
    ;; TODO: record types
    (type ((t-fun) $1))
    (t-fun ((t-fun-) (annotate! $1)))
    (t-fun-
     ((t-arg)           $1)
     ((t-arg ->  t-fun) (t-fun 'disc $1 $3))
     ((t-arg ~>  t-fun) (t-fun 'mono $1 $3))
     ((t-arg ->+ t-fun) (t-fun 'mono $1 $3))
     ((t-arg ->- t-fun) (t-fun 'anti $1 $3)))
    (t-arg
     ((t-product) (match $1
                    [(list x) x]
                    [xs (annotate! (t-tuple xs))])))

    (t-product
     ((t-factor)              (list $1))
     ((t-factor × t-product)  (cons $1 $3))
     ((t-factor * t-product)  (cons $1 $3)))
    (t-factor ((t-factor-) (annotate! $1)))
    (t-factor-
     ((t-atom)                      $1)
     ((t-sum)                       (t-sum $1)))

    (t-sum
     ((t-ctor) $1)
     ((t-ctor BAR t-sum)
      (hash-union-with $1 $3 (lambda () (error "duplicate constructor")))))
    (t-ctor
     ((Id)              (hash $1 '()))
     ((Id LP t-list RP) (hash $1 $3)))

    (t-atom ((t-atom-) (annotate! $1)))
    (t-atom-
     ((id) (if (base-type? $1) (t-base $1) (t-name $1)))
     ((LP t-paren RP)                 $2)
     ;; TODO: error on duplicate field names
     ((LSQUARE t-fields RSQUARE)      (t-record (make-immutable-hash $2)))
     ((LCURLY t-paren RCURLY)         (t-set $2))
     ((LCURLY type : t-paren RCURLY)  (t-map $2 $4)))

    ;; `t-paren' is a type inside parentheses or similar.
    (t-paren ((t-paren-) (annotate! $1)))
    (t-paren-
     (()                    (t-tuple '()))
     ((type)                $1)
     ((type COMMA t-list)   (t-tuple (cons $1 $3))))
    (t-list
     (()                   '())
     ((type)               (list $1))
     ((type COMMA t-list)  (cons $1 $3)))

    (t-fields (() '())
              ((t-field) (list $1))
              ((t-field COMMA t-fields) (cons $1 $3)))
    (t-field ((name : type) (cons $1 $3)))

    ;; ----- literals -----
    (lit ((number)      $1)
         ((string)      $1)
         ((TRUE)        '#t)
         ((FALSE)       '#f))

    ;; ----- patterns -----
    (pat ((pat-) (annotate! $1)))
    (pat-
     ((name)            (p-var $1))
     ((lit)             (p-lit $1))
     ((_)               (p-wild))
     ((DOT expr)        (p-eq $2))
     ((BANG expr)       (p-eq $2))
     ;; TODO: precedence, associativity of `|', `&'
     ((pat BAR pat)     (p-or (list $1 $3)))
     ((pat & pat)       (p-and (list $1 $3)))
     ((LP pat RP)       $2)
     ;; TODO: patterns for records
     ((LP p-list* RP)   (p-tuple $2))
     ((Id)              (p-tag $1 '()))
     ((Id LP p-list RP) (p-tag $1 $3)))
    (p-list* (() '())
             ((pat COMMA p-list) (cons $1 $3)))
    (p-list ((p-list*) $1)
            ((pat)         (list $1)))

    ;; ----- expressions -----
    (expr ((expr-) (annotate! $1)))
    (expr-
     ((LAMBDA names => expr)        (e-lam* $2 $4))
     ((LET decls IN expr)           (e-let-decls $2 $4))
     ((CASE e-op cases)             (e-case $2 $3))
     ((IF e-op THEN e-op ELSE e-op) (e-if $2 $4 $6))
     ((WHEN LP e-op RP expr)        (e-cond 'mono $3 $5))
     ((UNLESS LP e-op RP expr)      (e-cond 'anti $3 $5))
     ;; TODO: syntax for tuple fixpoints? (FIX pat = expr)?
     ((FIX name is e-bars)          (e-fix $2 $4))
     ((FIX name : type is e-bars)   (e-ann $4 (e-fix $2 $6)))
     ;; TODO: is this syntax used at all? should it be?
     ((FIX LP name RP expr)         (e-fix $3 $5))
     ((FIX LP name : type RP expr)  (e-ann $5 (e-fix $3 $7)))
     ;; TODO: change for loop syntax
     ;;   from "for (LOOPS) EXPR"
     ;;   to "for LOOPS: EXPR" or similar
     ((⋁ LP loops RP expr)          (e-loop $3 $5))
     ;; TODO: eliminate this old syntax.
     ((FOR LP loops RP expr)        (e-loop $3 $5))
     ;; this seems to work in practice, although it causes lots of shift-reduce
     ;; conflicts
     ;; TODO: should we use e-bars here?
     ((FOR loops : expr)            (e-loop $2 $4))
     ((e-op : type)                 (e-ann $3 $1))
     ((e-op)                        $1))
    (e-op ((e-op-) (annotate! $1)))
    (e-op-
     ;; for now, everything is left associative. TODO: precedence parsing.
     ((e-op e-oper e-app)    (e-app (e-app $2 $1) $3))
     ((e-op ∨ e-app)         (e-lub (list $1 $3)))
     ((e-op LUB e-app)       (e-lub (list $1 $3)))
     ((e-op IN? e-app)       (e-in? $1 $3))
     ((Id LP e-list RP)      (e-tag $1 $3))
     ((Id)                   (e-tag $1 '()))
     ((e-app)                $1))
    (e-oper
     ((oper) (annotate! (if (prim? $1) (e-prim $1) (e-var $1)))))
    (e-app
     ((e-app e-atom)   (annotate! (e-app $1 $2)))
     ((e-atom)         $1))
    (e-atom ((e-atom-) (annotate! $1)))
    (e-atom-
     ((e-atom DOT name)                 (e-proj $3 $1))
     ;; TODO: this could produce confusion with floating point numbers.
     ((e-atom DOT number)               (e-proj $3 $1))
     ((name)                            (if (prim? $1) (e-prim $1) (e-var $1)))
     ((lit)                             (e-lit $1))
     ((EMPTY)                           (e-lub '()))
     ((LP expr RP)                      $2)
     ((LP expr BAR loops RP)            (e-loop $4 $2))
     ((LP e-list* RP)                   (e-tuple $2))
     ;; records
     ;; TODO: use paren-based syntax for records everywhere. this requires:
     ;; 1. unifying the empty record type & the empty tuple type
     ;;    or maybe just make '(:) the empty record or something?
     ;;    need to think about impl strategy, too.
     ;;    maybe just make empty p-tuple and p-record compile to wildcard '_.
     ;; 2. figuring out what to do about type-ascription exprs (expr : type)!
     ;;
     ;; TODO: error on duplicate field identifiers.
     ((LSQUARE e-fields RSQUARE)        (e-record (make-immutable-hash $2)))
     ;; sets, set comprehensions
     ((LCURLY e-list RCURLY)            (e-set $2))
     ((LCURLY e-op BAR loops RCURLY)    (e-loop $4 (e-set (list $2))))
     ;; maps
     ((LCURLY : RCURLY)                 (e-map '()))
     ((LCURLY e-kv-list1 RCURLY)        (e-map $2)))

    (e-fields (() '())
              ((e-field)                (list $1))
              ((e-field COMMA e-fields) (cons $1 $3)))
    (e-field  ((name : expr)            (cons $1 $3)))

    (e-kv ((e-op : e-op) (list $1 $3)))
    (e-kv-list1
     ((e-kv)                  (list $1))
     ((e-kv COMMA e-kv-list1) (cons $1 $3)))

    ;; an expr or a nonempty bar-separated list of exprs; if the latter,
    ;; interpreted as lub-ing the exprs together.
    (e-bars ((bar-exprs) (match $1 [(list x) x] [xs (e-lub xs)])))

    ;; at least one expr, separated and/or started by BARs. more than one BAR is
    ;; allowed between or before exprs.
    (bar-exprs
     ((expr)                (list $1))
     ((BAR bar-exprs)       $2)
     ((expr BAR bar-exprs)  (cons $1 $3)))

    (e-list
     ((e-list*) $1)
     ((e-op) (list $1)))
    (e-list*
     (() '())
     ((e-op COMMA e-list) (cons $1 $3)))

    (cases (() '()) ((case cases) (cons $1 $2)))
    (case  ((BAR pat => expr) (annotate! (case-branch $2 $4))))

    (loops
     (() '())
     ((loop) (list $1))
     ((loop COMMA loops) (cons $1 $3)))
    (loop
     ((e-op)         (l-cond 'mono $1))
     ((pat IN e-op)  (l-in $1 $3))
     ((pat ∈ e-op)   (l-in $1 $3))))))



;; ========== SOURCE INFO MAGIC ==========
;; Takes (current-source-name) and the start/end position given by
;; parser-tools/yacc, and produces a srcloc.
(define (make-source start-pos end-pos)
  (match-define (position start line column) start-pos)
  (define span (- (position-offset end-pos) start))
  (srcloc (current-source-name) line column start span))

;; Magic variable-capturing macro that produces the current source info when
;; used inside of a grammar production rule.
(define-syntax-parser current-source-info
  [(self) #'(current-source-info self)]
  [(_ ctx) (with-syntax ([start-pos (datum->syntax #'ctx '$1-start-pos)]
                         [end-pos   (datum->syntax #'ctx '$n-end-pos)])
             #'(make-source start-pos end-pos))])

;; Annotates a value with the current source info.
(define-syntax-parser annotate!
  [(_ e ctx) #'(with-source! e (current-source-info ctx))]
  [(_ e) #'(annotate! e e)]
  [self:id #'(lambda (e) (annotate! e self))])


;; ========== SYNTAX SUGAR ==========
;; TODO?: syntax sugar for projecting a set of fields from a record?
(define (e-lam* ids body) (foldr e-lam body ids))

(define (e-if cnd thn els)
  (e-case cnd `(,(case-branch (p-lit #t) thn)
                ,(case-branch (p-lit #f) els))))

(define (e-let-decls decls body)
  (e-let-defns (decls->defns decls #:default-tone 'mono) body))
(define (e-let-defns defns body)
  (for/fold ([body body]) ([d (reverse defns)])
    (match d
      [(d-type name type) (e-let-type name type body)]
      [(d-val name tone type expr)
       (e-let tone name (if type (e-ann type expr) expr) body)])))

(enum loop
  (l-in pat expr)
  (l-cond tone expr))

(define (e-loop loops body)
  (match loops
    ['() body]
    [(cons (l-in p e) ls)      (e-set-bind p e (e-loop ls body))]
    [(cons (l-cond tone e) ls) (e-cond tone e (e-loop ls body))]))

(define (e-in? elt-exp set-exp)
  (e-loop (list (l-in (p-eq elt-exp) set-exp))
          (e-lit #t)))


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
;;   (set! defns (decls->defns decls))
;;   (eval-defns! defns))
