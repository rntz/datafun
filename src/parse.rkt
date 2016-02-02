#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.
;; also, "pretty printers", i.e. convert parsed things back to canonical sexps.
;; TODO: an exception class for parse failures.

;; we only consider prefix forms. so =, :, etc. are not included.
;; we don't reuse tone? because 'any isn't a decl form.
(define decl-form? (or/c 'type 'mono 'anti 'fix))
(define loop-form? (or/c 'for 'when 'unless))
(define expr-form?
  (or/c 'as 'case 'cons 'extend-record 'fix 'for 'if 'let 'lub 'make-map 'map
        'proj 'quote 'record 'record-merge 'set 'tag 'trustme 'unless 'when
        'λ 'π))
(define ident-reserved? (or/c expr-form? decl-form? loop-form?))
(define type-ident-reserved? base-type?)

(define (ident? x) (and (symbol? x) (not (ident-reserved? x))))
(define (type-ident? x) (and (symbol? x) (not (type-ident-reserved? x))))

(define arrow? (or/c '-> '~> '->+ '->-))


;;; Expression parsing/pretty-printing
(define (expr->sexp e)
  (compact-expr
   (match e
     [(e-var n) n]
     [(e-lit v) v]
     [(e-prim p) p]
     [(e-ann t e) `(as ,(type->sexp t) ,(expr->sexp e))]
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
     [(e-tag t es) `(',t ,@(map expr->sexp es))]
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
     [(e-map-for x key-set body)
      `(make-map ,x ,(expr->sexp key-set) ,(expr->sexp body))]
     [(e-set-bind pat arg body)
      `(,(expr->sexp body) for ,(pat->sexp pat) in ,(expr->sexp arg))]
     [(e-map-bind key-pat val arg body)
      `(,(expr->sexp body) for ,(pat->sexp key-pat) ,val in ,(expr->sexp arg))]
     [(e-cond 'mono subj body) `(when   ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-cond 'anti subj body) `(unless ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-fix var body) `(fix ,var ,(expr->sexp body))]
     [(e-let tone var expr body)
      `(let ([,@(match tone ['any '()] ['mono '(mono)] ['anti '(anti)])
              ,var = ,(expr->sexp expr)])
         ,(expr->sexp body))]
     [(e-let-type name type body)
      `(let ([type ,name = ,(type->sexp type)])
         ,(expr->sexp body))]
     [(e-trustme e) `(trustme ,(expr->sexp e))])))

(define (parse-expr expr)
  (match (expand-expr expr)
    [(? prim? p) (e-prim p)]
    [(? lit? l) (e-lit l)]
    [(? ident? v) (e-var v)]
    [`(let ,decls ,body)
     (parse-expr-letting (parse-decls decls) body)]
    [`(as ,t ,e) (e-ann (parse-type t) (parse-expr e))]
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
    [`',(? symbol? name) (e-tag name '())]
    [(or `(tag ,name . ,es) `(',name . ,es)) #:when (symbol? name)
     (e-tag name (map parse-expr es))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (parse-expr subj)
        (for/list ([p ps] [e es])
          (case-branch (parse-pat p) (parse-expr e))))]
    [`(lub . ,es) (e-lub (map parse-expr es))]
    [`(set . ,es) (e-set (map parse-expr es))]
    [(or `(make-map ,k ,key-set ,expr)
         `(map (,k ,expr) for ,(? symbol? k) in ,key-set))
     (e-map-for k (parse-expr key-set) (parse-expr expr))]
    [`(map (,ks ,vs) ...) (e-map (map (lambda l (map parse-expr l)) ks vs))]
    [`(get ,d ,k) (e-map-get (parse-expr d) (parse-expr k))]
    [`(set-bind ,pat ,arg ,body)
     (e-set-bind (parse-pat pat) (parse-expr arg) (parse-expr body))]
    [`(map-bind ,key-pat ,val ,arg ,body)
     (e-map-bind (parse-pat key-pat) val (parse-expr arg) (parse-expr body))]
    [`(when ,subj ,body)   (e-cond 'mono (parse-expr subj) (parse-expr body))]
    [`(unless ,subj ,body) (e-cond 'anti (parse-expr subj) (parse-expr body))]
    [`(fix ,x ,body) (e-fix x (parse-expr body))]
    [`(trustme ,e) (e-trustme (parse-expr e))]
    [(and e `(,f ,as ...))
     (if (expr-form? f)
         (error (format "invalid use of ~a: ~s" f e))
         (foldl (flip e-app) (parse-expr f) (map parse-expr as)))]
    [e (error "unfamiliar expression:" e)]))


;; expands out syntax sugar. not all syntax sugar goes here, though; for
;; example, in some sense 'let is syntax sugar.
(define (expand-expr e)
  (define expanded (expand-expr-once e))
  (if (eq? e expanded) e (expand-expr expanded)))

;; checks whether something "looks like" a set of loop clauses.
;; in:                   ((set 2) for x in X when (< x 3))
;; the loop clauses are:         (for x in X when (< x 3))
(define loop-clauses? (cons/c loop-form? any/c))

(define/match (expand-expr-once expr)
  [('empty) '(lub)]
  [(`(union . ,es)) `(lub . ,es)] ;; useful for readability
  [(`(,expr where . ,decls)) `(let ,decls ,expr)]
  [(`(if ,cnd ,thn ,els)) `(case ,cnd [#t ,thn] [#f ,els])]
  [(`(fix ,name ,exprs ...)) #:when (not (= 1 (length exprs)))
   `(fix ,name (lub ,@exprs))]
  ;; lub-comprehensions
  [(`(,(? (not/c expr-form?) e) . ,(? loop-clauses? clauses)))
   (expand-loop clauses e)]
  ;; set-comprehensions
  [(`(set ,(? (not/c expr-form?) es) ... . ,(? loop-clauses? clauses)))
   `((set ,@es) ,@clauses)]
  [(e) e])

(define (expand-loop clauses body)
  (match clauses
    ['() body]
    [`(for ,p in ,e . ,rest) `(set-bind ,p ,e ,(expand-loop rest body))]
    [`(for ,p ,v in ,e . ,rest) `(map-bind ,p ,v ,e ,(expand-loop rest body))]
    [`(when ,e . ,rest)   `(when ,e ,(expand-loop rest body))]
    [`(unless ,e . ,rest) `(unless ,e ,(expand-loop rest body))]))

;; applies syntax sugar to make expressions prettier
(define/match (compact-expr expr)
  [('(lub)) 'empty]
  [(`(case ,cnd [#t ,thn] [#f ,els])) `(if ,cnd ,thn ,els)]
  [(`(let ,decls-1 (let ,decls-2 ,body))) `(let (,@decls-1 ,@decls-2) ,body)]
  [(`(λ ,x (λ . ,rest))) `(λ ,x . ,rest)]
  [(`(fix ,name (lub . ,exprs))) #:when (not (= 1 (length exprs)))
   `(fix ,name ,@exprs)]
  [(`(set-bind ,p ,e ,body)) (compact-expr `(,body for ,p in ,e))]
  ;; compacting comprehensions is slightly complicated
  [(`((,(and form (or 'when 'unless)) ,cnd ,e) . ,(? loop-clauses? clauses)))
   `(,e ,@clauses ,form ,cnd)]
  [(`((,(? (not/c expr-form?) e) . ,(? loop-clauses? inner))
      . ,(? loop-clauses? outer)))
   `(,e ,@outer ,@inner)]
  [(e) e])


;;; Type parsing/pretty-printing
(define (type->sexp t)
  (define (hash->sexps h)
    (for/list ([(name type) h])
      `(,name ,(type->sexp type))))
  (match t
    [(t-name name) name]
    [(t-base name) name]
    [(t-tuple ts) `(* ,@(map type->sexp ts))]
    [(t-record fields)
     `(record ,@(for/list ([(name type) fields])
                  `(,name ,(type->sexp type))))]
    [(t-sum branches)
     `(+ ,@(for/list ([(name types) branches])
             `(,name ,@(map type->sexp types))))]
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
    [(? symbol?) (t-name t)]
    [`(* ,as ...) (t-tuple (map parse-type as))]
    [`(record (,ns ,ts) ...)
     (t-record (for/hash ([n ns] [t ts])
                 (values n (parse-type t))))]
    [`(+ . ,branches)
     (t-sum (for/hash ([b branches])
              (match b
                [(? symbol? name) (values name '())]
                [(cons name types) (values name (map parse-type types))])))]
    [`(,_ ... ,(? arrow?) ,_) (parse-arrow-type t)]
    [`(set ,a) (t-set (parse-type a))]
    [`(rel . ,as) (t-set (t-tuple (map parse-type as)))] ;; syntax sugar
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
    [(p-tuple ps) `(cons ,@(map pat->sexp ps))]
    [(p-tag name pats) `(',name ,@(map pat->sexp pats))]
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
    [`',(? symbol? name) (p-tag name '())]
    [(or `(tag ,name . ,pats) `(',name . ,pats))
      (p-tag name (map parse-pat pats))]
    [`(or ,ps ...) (p-or (map parse-pat ps))]
    [`(and ,ps ...) (p-and (map parse-pat ps))]
    [`(let ,x ,e ,p) (p-let x (parse-expr e) (parse-pat p))]
    [`(let ,x ,e ,ps ..1) (parse-pat `(let ,x ,e (p-and ,@ps)))]
    ;; matches a value equal to e
    [`(= ,e)
     (define t (gensym 'tmp))           ;bleh, gensym
     (parse-pat `(let ,t (= ,t ,e) #t))]
    [_ (error "unfamiliar pattern:" p)]))


;; Declaration/definition parsing
;;
;; for now, we don't support referring to a variable before its definition, not
;; even if you give it a type-signature. also, all recursion must be explicit.
(enum defn
  ;; type definition
  (d-type name type)
  ;; value definition
  ;; tone is either 'any, 'mono, or 'anti
  ;; type is #f if no type signature provided.
  (d-val name tone type expr))

(define tone-sigs (make-parameter #f))
(define type-sigs (make-parameter #f))
(define (set-type! name type) (hash-set! (type-sigs) name type))
(define (set-tone! name tone) (when tone (hash-set! (tone-sigs) name tone)))

;; this interface is not great :(
(define-syntax-rule (with-decl-parser body ...)
  (parameterize ([tone-sigs (make-hash)]
                 [type-sigs (make-hash)])
    body ...))

(define (parse-decls ds)
  (with-decl-parser
    (begin0 (generate/list (parse-decls! ds))
      (decl-parsing-done!))))

(define (decl-parsing-done!)
  ;; check that we don't have any left over unfulfilled type or tonicity
  ;; ascriptions for variables we haven't defined.
  (for ([(n _) (type-sigs)])
    (error "type signature for undefined variable:" n))
  (for ([(n _) (tone-sigs)])
    (error "tone signature for undefined variable:" n)))

(define (parse-decls! ds)
  (for ([d ds]) (parse-decl! d)))

(define (parse-decl! d)
  (define tone
    (match d
      [(cons (? tone? t) ds) (set! d ds) t]
      [_ #f]))

  (define (d-val! name expr)
    (set-tone! name tone)
    (define the-tone (hash-ref (tone-sigs) name 'any))
    (define the-type (hash-ref (type-sigs) name #f))
    (hash-remove! (tone-sigs) name)
    (hash-remove! (type-sigs) name)
    (yield (d-val name the-tone the-type (parse-expr expr))))

  (match d
    ;; type declaration
    [`(type ,(? type-ident? name) = ,type)
     (yield (d-type name (parse-type type)))]

    ;; just a tonicity declaration
    [`(,(? ident? names) ...) #:when tone
     (for ([n names]) (set-tone! n tone))]

    ;; type declaration
    [`(,(? ident? names) ... : ,t ..1)
     (define type (parse-arrow-type t))
     (for ([n names])
       (set-tone! n tone)
       (set-type! n type))]

    ;; a fixpoint value declaration
    ;; TODO: generalize to allow mutual recursion?
    [`(fix ,(? ident? name) = . ,body)
     (d-val! name `(fix ,name ,(expand-body body)))]

    ;; TODO: irrefutable pattern declarations
    ;; a value or function declaration
    [`(,(? ident? name) ,(? ident? args) ... = . ,body)
     (d-val! name `(λ ,@args ,(expand-body body)))]

    [_ (error "could not parse declaration:" d)]))

(define/match (expand-body body)
  [(`(,expr)) expr]
  [(`(,_ where . ,_)) body])

;; given some defns and an unparsed expr, parses the expr in the appropriate
;; environment and produces an expr which let-binds all the defns in the expr.
(define (parse-expr-letting defns e)
  (set! e (parse-expr e))
  (for/fold ([e e]) ([d (reverse defns)])
    (match d
      [(d-val n k t body) (e-let k n (if t (e-ann t body) body) e)]
      [(d-type name type) (e-let-type name type e)])))
