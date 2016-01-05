#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.
;; also, "pretty printers", i.e. convert parsed things back to canonical sexps.
;; TODO: an exception class for parse failures.

;; only prefix syntax forms are relevant here. thus =, ->, etc. not included.
(define (reserved? x) (set-member? reserved x))
(define reserved
  (list->set '(case cons empty extend-record fix fn if isa join let mono
               proj quote record record-merge set tag trustme when where λ π)))

(define (ident? x) (and (symbol? x) (not (reserved? x))))


;;; Expression parsing/pretty-printing
(define (expr->sexp e)
  (compact-expr
   (match e
     [(e-var n) n]
     [(e-lit v) v]
     [(e-prim p) p]
     [(e-ann t e) `(isa ,(type->sexp t) ,(expr->sexp e))]
     [(e-lam v b) `(fn ,v ,(expr->sexp b))]
     [(e-app f a)
      (let loop ([func f] [args (list a)])
        (match func
          [(e-app f a) (loop f (cons a args))]
          [_ (map expr->sexp (cons func args))]))]
     [(e-tuple es) `(cons ,@(map expr->sexp es))]
     [(e-proj i e) `(π ,i ,(expr->sexp e))]
     [(e-record fs) `(record ,@(for/list ([(n e) fs])
                                 `(,n ,(expr->sexp e))))]
     [(e-record-merge l r) `(record-merge ,(expr->sexp l) ,(expr->sexp r))]
     [(e-tag t e) `(',t ,(expr->sexp e))]
     [(e-case subj branches)
      `(case ,(expr->sexp subj)
         ,@(for/list ([b branches])
             (match-define (case-branch pat body) b)
             `(,(pat->sexp pat) ,(expr->sexp body))))]
     [(e-join '()) 'empty]
     [(e-join l) `(join ,@(map expr->sexp l))]
     [(e-set es) `(set ,@(map expr->sexp es))]
     [(e-join-in var arg body)
      `(for ([,var ,(expr->sexp arg)]) ,(expr->sexp body))]
     [(e-fix var body) `(fix ,var ,(expr->sexp body))]
     [(e-let tone var expr body)
      `(let ([,@(match tone ['mono '(mono)] ['any '()])
              ,var = ,(expr->sexp expr)])
         ,(expr->sexp body))]
     [(e-trustme e) `(trustme ,(expr->sexp e))])))

(define (parse-expr e)
  (match (expand-expr e)
    [(? prim?) (e-prim e)]
    [(? lit?) (e-lit e)]
    [(? ident?) (e-var e)]
    [`(isa ,t ,e) (e-ann (parse-type t) (parse-expr e))]
    [`(,(or 'fn 'λ) ,xs ... ,e)
     (set! e (parse-expr e))
     (foldr e-lam e xs)]
    [`(cons . ,es) (e-tuple (map parse-expr es))]
    [`(,(or 'π 'proj) ,i ,e) (e-proj i (parse-expr e))]
    [`(record (,ns ,es) ...) (e-record (for/hash ([n ns] [e es])
                                         (values n (parse-expr e))))]
    [`(record-merge ,a ,b) (e-record-merge (parse-expr a) (parse-expr b))]
    [`(extend-record ,base . ,as)
     (e-record-merge (parse-expr base) (parse-expr `(record . ,as)))]
    [(or `(tag ,name ,e) `(',name ,e)) (e-tag name (parse-expr e))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (parse-expr subj)
        (for/list ([p ps] [e es])
          (case-branch (parse-pat p) (parse-expr e))))]
    [`(join . ,es) (e-join (map parse-expr es))]
    [`(set . ,es) (e-set (map parse-expr es))]
    [`(let ,decls ,body)
     (parse-expr-letting (parse-all-decls decls) body)]
    [`(for () ,body) (parse-expr body)]
    [`(for ([,name ,expr]) ,body)
     (e-join-in name (parse-expr expr) (parse-expr body))]
    [`(for ([,name ,expr] ,clauses ..1) ,body)
     (parse-expr `(for ([,name ,expr]) (for ,clauses ,body)))]
    [`(fix ,x ,body) (e-fix x (parse-expr body))]
    [`(trustme ,e) (e-trustme (parse-expr e))]
    [`(,f ,as ...)
     (if (reserved? f)
         (error "invalid use of reserved form:" e)
         (foldl (flip e-app) (parse-expr f) (map parse-expr as)))]
    [_ (error "unfamiliar expression:" e)]))


;; expands out syntax sugar. not all syntax sugar goes here, though; for
;; example, in some sense 'let is syntax sugar.
(define (expand-expr expr)
  (match expr
    ['empty '(join)]
    [`(,expr where . ,decls) `(let ,decls ,expr)]
    [`(if ,cnd ,thn ,els) `(case ,cnd [#t ,thn] [#f ,els])]
    [e e]))

;; applies syntax sugar to make expressions prettier
(define (compact-expr expr)
  (match expr
    ['(join) 'empty]
    [`(case ,cnd [#t ,thn] [#f ,els]) `(if ,cnd ,thn ,els)]
    [`(for ,clauses-1 (for ,clauses-2 ,body))
     `(for ,(append clauses-1 clauses-2) ,body)]
    [`(let ,decls-1 (let ,decls-2 ,body))
     `(let ,(append decls-1 decls-2) ,body)]
    [e e]))


;;; Type parsing/pretty-printing
(define (type->sexp t)
  (define (hash->sexps h)
    (for/list ([(name type) h])
      `(,name ,(type->sexp type))))
  (match t
    [(t-bool) 'bool]
    [(t-nat) 'nat]
    [(t-str) 'str]
    [(t-tuple ts) `(* ,@(map type->sexp ts))]
    [(t-record fields) `(record ,@(hash->sexps fields))]
    [(t-sum branches) `(+ ,@(hash->sexps branches))]
    [(t-set a) `(set ,(type->sexp a))]
    [(t-fun tone a b)
     (let loop ([args (list a)] [result b])
       (match result
         [(t-fun tone2 a b) #:when (equal? tone tone2)
          (loop (cons a args) b)]
         [_ `(,@(map type->sexp (reverse args))
              ,(match tone ['any '->] ['mono '~>])
              ,(type->sexp result))]))]))

(define (parse-type t)
  (match t
    ['bool (t-bool)]
    ['nat (t-nat)]
    ['str (t-str)]
    [`(* ,as ...) (t-tuple (map parse-type as))]
    [`(record (,ns ,ts) ...)
     (t-record (for/hash ([n ns] [t ts])
                 (values n (parse-type t))))]
    [`(+ (,tags ,types) ...)
      (t-sum (for/hash ([tag tags] [type types])
               (values tag (parse-type type))))]
    [`(,_ ... ,(or '-> '~>) ,_) (parse-arrow-type t)]
    [`(set ,a) (t-set (parse-type a))]
    [_ (error "unfamiliar type:" t)]))

(define (arrow-type->sexp t)
  (match t
    [(t-fun _ _ _) (type->sexp t)]
    [_ `(,(type->sexp t))]))

(define (parse-arrow-type t)
  (define (parse tone as bs)
    (foldr (curry t-fun tone) (parse-arrow-type bs) (map parse-type as)))
  (match t
    [`(,(and as (not '-> '~>)) ... -> ,bs ..1) (parse 'any as bs)]
    [`(,(and as (not '-> '~>)) ... ~> ,bs ..1) (parse 'mono as bs)]
    [`(,t) (parse-type t)]))


;; Pattern parsing/pretty-printing
(define (pat->sexp p)
  (match p
    [(p-wild) '_]
    [(p-var x) x]
    [(p-lit x) x]
    [(p-tuple ps) `(cons ,(map pat->sexp ps))]
    [(p-tag name p) `(',name ,(pat->sexp p))]))

(define (parse-pat p)
  (match p
    ['_ (p-wild)]
    [(? ident?) (p-var p)]
    [(? lit?) (p-lit p)]
    [`(cons ,ps ...) (p-tuple (map parse-pat ps))]
    [(or `(tag ,name ,pat) `(',name ,pat))
      (p-tag name (parse-pat pat))]
    [_ (error "unfamiliar pattern:" p)]))


;;; Declaration/definition parsing
;; TODO?: defn->sexp

;; A definition.
;; tone is either 'any or 'mono
;; type is #f if no type signature provided.
(struct defn (name tone type expr) #:transparent)

(struct decl-state (tone-sigs type-sigs) #:transparent)

(define empty-decl-state (decl-state (hash) (hash)))

(define (parse-all-decls ds)
  (define-values (new-state defns) (parse-decls empty-decl-state ds))
  (match-define (decl-state tone-sigs type-sigs) new-state)
  (for ([(n _) type-sigs])
    (error "type ascription for undefined variable:" n))
  (for ([(n _) tone-sigs])
    (error "monotonicity declaration for undefined variable:" n))
  defns)

;; returns (values new-state list-of-defns), or errors
;;
;; for now, we don't support referring to a variable before its definition, not
;; even if you give it a type-signature. also, all recursion must be explicit.
(define (parse-decls state ds)
  (define defns '())
  (for ([d ds])
    (define-values (new-state new-defns) (parse-decl state d))
    (set! state new-state)
    (set! defns (rev-append new-defns defns)))
  (values state (reverse defns)))

;; returns (values new-state list-of-defns), or errors
(define (parse-decl state d)
  (match-define (decl-state tone-sigs type-sigs) state)
  (define (ret x) (values (decl-state tone-sigs type-sigs) x))
  (define mono (match (car d)
                 ['mono (set! d (cdr d)) #t]
                 [_ #f]))
  (define (set-mono! n)
    (set! tone-sigs (hash-set tone-sigs n 'mono)))
  (define (set-type! n t)
    (set! type-sigs (hash-set type-sigs n t)))
  (match d
    ;; just a monotonicity declaration
    [`(,(? ident? names) ...) #:when mono
     (for ([n names]) (set-mono! n))
     (ret '())]
    ;; type declaration
    [`(,(? ident? names) ... : ,t ..1)
     (define type (parse-arrow-type t))
     (for ([n names])
       (when mono (set-mono! n))
       (set-type! n type))
     (ret '())]
    ;; a value declaration
    [`(,(? ident? name) ,(? ident? args) ... = . ,body)
     (when mono (set-mono! name))
     (define expr
       `(λ ,@args
          ,(match body
             [`(,expr) expr]
             [`(,expr where . ,decls) body])))
     ;; grab tone & type
     (define tone (hash-ref tone-sigs name 'any))
     (define type (hash-ref type-sigs name #f))
     (set! tone-sigs (hash-remove tone-sigs name))
     (set! type-sigs (hash-remove type-sigs name))
     ;; parse the decl & give it up.
     (ret (list (defn name tone type (parse-expr expr))))]
    [_ (error "could not parse declaration:" d)]))

;; given some defns and an unparsed expr, parses the expr in the appropriate
;; environment and produces an expr which let-binds all the defns in the expr.
(define (parse-expr-letting defns e)
  (set! e (parse-expr e))
  (for/fold ([e e]) ([d (reverse defns)])
    (match-define (defn n k t body) d)
    (e-let k n (if t (e-ann t body) body) e)))
