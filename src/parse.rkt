#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.
;; also, "pretty printers", i.e. convert parsed things back to canonical sexps.
;; TODO: an exception class for parse failures.

;; only prefix syntax forms are relevant here. thus =, ->, etc. not included.
(define (reserved? x) (set-member? reserved x))
(define reserved
  ;; TODO: e-map-for
  ;; TODO: rename 'isa to 'as
  (list->set '(case cons empty extend-record fix fn for for/set get if isa lub
               let map mono proj quote record record-merge set tag trustme
               unless when λ π)))

(define (arrow? x) (set-member? arrows x))
(define arrows (list->set '(-> ~> ->+ ->-)))

(define (ident? x) (and (symbol? x) (not (reserved? x))))


;;; Expression parsing/pretty-printing
(define (expr->sexp e)
  (compact-expr
   (match e
     [(e-var n) n]
     [(e-lit v) v]
     [(e-prim p) p]
     [(e-ann t e) `(isa ,(type->sexp t) ,(expr->sexp e))]
     [(e-lam v b) `(λ ,v ,(expr->sexp b))]
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
     [(e-lub '()) 'empty]
     [(e-lub l) `(lub ,@(map expr->sexp l))]
     [(e-set es) `(set ,@(map expr->sexp es))]
     [(e-map kvs) `(map ,@(map (curry map expr->sexp) kvs))]
     [(e-map-get d k) `(get ,(expr->sexp d) ,(expr->sexp k))]
     [(e-set-bind pat arg body)
      `(for ([,(pat->sexp pat) ,(expr->sexp arg)]) ,(expr->sexp body))]
     [(e-cond 'mono subj body) `(when   ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-cond 'anti subj body) `(unless ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-fix var body) `(fix ,var ,(expr->sexp body))]
     [(e-let tone var expr body)
      `(let ([,@(match tone ['any '()] ['mono '(mono)] ['anti '(anti)])
              ,var = ,(expr->sexp expr)])
         ,(expr->sexp body))]
     [(e-trustme e) `(trustme ,(expr->sexp e))])))

(define (parse-expr expr)
  (match (expand-expr expr)
    [(? prim? p) (e-prim p)]
    [(? lit? l) (e-lit l)]
    [(? ident? v) (e-var v)]
    [`(let ,decls ,body)
     (parse-expr-letting (parse-all-decls decls) body)]
    [`(isa ,t ,e) (e-ann (parse-type t) (parse-expr e))]
    [`(,(or 'fn 'λ) ,xs ... ,e)
     (set! e (parse-expr e))
     (foldr e-lam e xs)]
    [`(cons . ,es) (e-tuple (map parse-expr es))]
    [`(,(or 'π 'proj) ,i ,e) (e-proj i (parse-expr e))]
    [`(record (,(? symbol? ns) ,es) ...)
     (e-record (for/hash ([n ns] [e es]) (values n (parse-expr e))))]
    [`(record-merge ,a ,b) (e-record-merge (parse-expr a) (parse-expr b))]
    [`(extend-record ,base . ,as)
     (e-record-merge (parse-expr base) (parse-expr `(record . ,as)))]
    [(or `(tag ,name ,e) `(',name ,e)) #:when (symbol? name)
     (e-tag name (parse-expr e))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (parse-expr subj)
        (for/list ([p ps] [e es])
          (case-branch (parse-pat p) (parse-expr e))))]
    [`(lub . ,es) (e-lub (map parse-expr es))]
    [`(set . ,es) (e-set (map parse-expr es))]
    [`(map (,ks ,vs) ...) (e-map (map (lambda l (map parse-expr l)) ks vs))]
    [`(get ,d ,k) (e-map-get (parse-expr d) (parse-expr k))]
    [`(set-bind ,pat ,arg ,body)
     (e-set-bind (parse-pat pat) (parse-expr arg) (parse-expr body))]
    [`(when ,subj ,body)   (e-cond 'mono (parse-expr subj) (parse-expr body))]
    [`(unless ,subj ,body) (e-cond 'anti (parse-expr subj) (parse-expr body))]
    [`(fix ,x ,body) (e-fix x (parse-expr body))]
    [`(trustme ,e) (e-trustme (parse-expr e))]
    [(and e `(,f ,as ...))
     (if (reserved? f)
         (error "invalid use of reserved form:" e)
         (foldl (flip e-app) (parse-expr f) (map parse-expr as)))]
    [e (error "unfamiliar expression:" e)]))


;; expands out syntax sugar. not all syntax sugar goes here, though; for
;; example, in some sense 'let is syntax sugar.
(define (expand-expr e)
  (let loop ([e e])
    (define expanded (expand-expr-once e))
    (if (eq? e expanded) e (loop expanded))))

(define/match (expand-expr-once expr)
  [('empty) '(lub)]
  [(`(,expr where . ,decls)) `(let ,decls ,expr)]
  [(`(if ,cnd ,thn ,els)) `(case ,cnd [#t ,thn] [#f ,els])]
  ;; for loop / lub comprehension syntax
  [(`(for () ,body)) body]
  [(`(for ([,pat ,expr] . ,clauses) ,body))
   `(set-bind ,pat ,expr (for ,clauses ,body))]
  [(`(for (#:when ,cnd . ,clauses) ,body))
   `(when ,cnd (for ,clauses ,body))]
  [(`(for (#:unless ,cnd . ,clauses) ,body))
   `(unless ,cnd (for ,clauses ,body))]
  ;; end for loop syntax
  [(`(for/set ,clauses ,body))
   `(for ,clauses (set ,body))]
  [(e) e])

;; applies syntax sugar to make expressions prettier
(define/match (compact-expr expr)
  [('(lub)) 'empty]
  [(`(case ,cnd [#t ,thn] [#f ,els])) `(if ,cnd ,thn ,els)]
  [(`(for ,clauses-1 (for ,clauses-2 ,body)))
   `(for ,(append clauses-1 clauses-2) ,body)]
  [(`(let ,decls-1 (let ,decls-2 ,body)))
   `(let ,(append decls-1 decls-2) ,body)]
  [(`(λ ,x (λ . ,rest))) `(λ ,x . ,rest)]
  [(e) e])


;;; Type parsing/pretty-printing
(define (type->sexp t)
  (define (hash->sexps h)
    (for/list ([(name type) h])
      `(,name ,(type->sexp type))))
  (match t
    [(t-base name) name]
    [(t-tuple ts) `(* ,@(map type->sexp ts))]
    [(t-record fields) `(record ,@(hash->sexps fields))]
    [(t-sum branches) `(+ ,@(hash->sexps branches))]
    [(t-set a) `(set ,(type->sexp a))]
    [(t-map k v) `(map ,(type->sexp k) ,(type->sexp v))]
    [(t-fun tone a b)
     (let loop ([args (list a)] [result b])
       (match result
         [(t-fun tone2 a b) #:when (equal? tone tone2)
          (loop (cons a args) b)]
         [_ `(,@(map type->sexp (reverse args))
              ,(match tone ['any '->] ['mono '~>] ['anti '->-])
              ,(type->sexp result))]))]))

(define (parse-type t)
  (match t
    [(? base-type?) (t-base t)]
    [`(* ,as ...) (t-tuple (map parse-type as))]
    [`(record (,ns ,ts) ...)
     (t-record (for/hash ([n ns] [t ts])
                 (values n (parse-type t))))]
    [`(+ (,tags ,types) ...)
      (t-sum (for/hash ([tag tags] [type types])
               (values tag (parse-type type))))]
    [`(,_ ... ,(? arrow?) ,_) (parse-arrow-type t)]
    [`(set ,a) (t-set (parse-type a))]
    [`(map ,k ,v) (t-map (parse-type k) (parse-type v))]
    [_ (error "unfamiliar type:" t)]))

(define (arrow-type->sexp t)
  (match t
    [(t-fun _ _ _) (type->sexp t)]
    [_ `(,(type->sexp t))]))

(define (parse-arrow-type t)
  (define (parse tone as bs)
    (foldr (curry t-fun tone) (parse-arrow-type bs) (map parse-type as)))
  (match t
    [`(,(and as (not (? arrow?))) ... ->  ,bs ..1) (parse 'any  as bs)]
    [`(,(and as (not (? arrow?))) ... ~>  ,bs ..1) (parse 'mono as bs)]
    [`(,(and as (not (? arrow?))) ... ->+ ,bs ..1) (parse 'mono as bs)]
    [`(,(and as (not (? arrow?))) ... ->- ,bs ..1) (parse 'anti as bs)]
    [`(,t) (parse-type t)]))


;; Pattern parsing/pretty-printing
(define (pat->sexp p)
  (match p
    [(p-wild) '_]
    [(p-var x) x]
    [(p-lit x) x]
    [(p-tuple ps) `(cons ,(map pat->sexp ps))]
    [(p-tag name p) `(',name ,(pat->sexp p))]
    [(p-or `(,p)) (pat->sexp p)]
    [(p-or pats) `(or ,@(map pat->sexp pats))]
    [(p-and `(,p)) (pat->sexp p)]
    [(p-and pats) `(and ,@(map pat->sexp pats))]
    [(p-let x (e-app (e-app (e-prim '=) (e-var y)) e) (p-lit #t))
     #:when (equal? x y)
     `(= ,(expr->sexp e))]
    [(p-let x e (p-and ps)) `(let ,x ,(expr->sexp e) ,@(map pat->sexp ps))]
    [(p-let x e p) `(let ,x ,(expr->sexp e) ,(pat->sexp p))]))

(define (parse-pat p)
  (match p
    ['_ (p-wild)]
    [(? ident?) (p-var p)]
    [(? lit?) (p-lit p)]
    [`(cons ,ps ...) (p-tuple (map parse-pat ps))]
    [(or `(tag ,name ,pat) `(',name ,pat))
      (p-tag name (parse-pat pat))]
    [`(or ,ps ...) (p-or (map parse-pat ps))]
    [`(and ,ps ...) (p-and (map parse-pat ps))]
    [`(let ,x ,e ,p) (p-let x (parse-expr e) (parse-pat p))]
    [`(let ,x ,e ,ps ..1) (parse-pat `(let ,x ,e (p-and ,@ps)))]
    ;; matches a value equal to e
    [`(= ,e)
     (define t (gensym 'tmp))           ;bleh, gensym
     (parse-pat `(let ,t (= ,t ,e) #t))]
    [_ (error "unfamiliar pattern:" p)]))


;;; Declaration/definition parsing
;; TODO?: defn->sexp
;;
;; TODO: "fix" decls; (fix x = ...) becomes (x = (fix x ...))
;; (nested to-do: how to generalize to mutual recursion?)

;; A definition.
;; tone is either 'any, 'mono, or 'anti
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
    (error "tonicity declaration for undefined variable:" n))
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
  (define decl-tone
    (match d
      [(cons (? tone? tone) d-rest) (set! d d-rest) tone]
      [_ #f]))
  (define (set-tone! n)
    (when decl-tone
     (set! tone-sigs (hash-set tone-sigs n decl-tone))))
  (define (set-type! n t)
    (set! type-sigs (hash-set type-sigs n t)))
  (match d
    ;; just a tonicity declaration
    [`(,(? ident? names) ...) #:when decl-tone
     (for ([n names]) (set-tone! n))
     (ret '())]
    ;; type declaration
    [`(,(? ident? names) ... : ,t ..1)
     (define type (parse-arrow-type t))
     (for ([n names])
       (set-tone! n)
       (set-type! n type))
     (ret '())]
    ;; a value declaration
    [`(,(? ident? name) ,(? ident? args) ... = . ,body)
     (set-tone! name)
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
