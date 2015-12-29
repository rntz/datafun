#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.

(define (reserved? x) (set-member? reserved x))
(define reserved
  (list->set '(: = mono <- -> ~>
               empty fn λ cons π proj record record-merge extend-record tag
               quote case if join set let where fix)))

(define (ident? x) (and (symbol? x) (not (reserved? x))))

;; contexts Γ are simple lists of identifiers - used to map variable names to
;; debruijn indices.
(define (parse-expr e Γ)
  (define (r e) (parse-expr e Γ))
  (match e
    [(? prim?) (e-prim e)]
    [(? lit?) (e-lit e)]
    ['empty (e-join '())]
    [(? ident?)
     (match (index-of e Γ)
       [#f (e-free-var e)]
       [i (e-var e i)])]
    [`(: ,t ,e) (e-ann (parse-type t) (r e))]
    [`(,(or 'fn 'λ) ,xs ... ,e)
      (set! e (parse-expr e (append (reverse xs) Γ)))
      (foldr e-lam e xs)]
    [`(cons . ,es) (e-tuple (map r es))]
    [`(,(or 'π 'proj) ,i ,e) (e-proj i (r e))]
    [`(record (,ns ,es) ...) (e-record (for/hash ([n ns] [e es])
                                         (values n (r e))))]
    [`(record-merge ,a ,b) (e-record-merge (r a) (r b))]
    [`(extend-record ,base . ,as) (e-record-merge (r base) (r `(record . ,as)))]
    [(or `(tag ,name ,e) `(',name ,e)) (e-tag name (r e))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (r subj)
        (for/list ([p ps] [e es])
          (set! p (parse-pat p))
          (set! e (parse-expr e (append (reverse (pat-vars p)) Γ)))
          (case-branch p e)))]
    [`(join . ,es) (e-join (map r es))]
    [`(set . ,es) (e-set (map r es))]
    [`(let ,decls ,body)
     (parse-expr-letting (parse-decls decls Γ) body Γ)]
    [`(,expr where . ,decls)
     (parse-expr-letting (parse-decls decls Γ) expr Γ)]
    [`(let ,x <- ,e in ,body)
      (e-letin x (r e) (parse-expr body (cons x Γ)))]
    [`(fix ,x ,body)
      (e-fix x (parse-expr body (cons x Γ)))]
    [`(,f ,as ...)
     (if (reserved? f)
         (error "invalid use of form:" e)
         (foldl (flip e-app) (r f) (map r as)))]
    [_ (error "unfamiliar expression:" e)]))

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
    [`(,as ... -> ,r) (parse-arrow-type t-fun as (parse-type r))]
    [`(,as ... ~> ,r) (parse-arrow-type t-mono as (parse-type r))]
    [`(set ,a) (t-fs (parse-type a))]
    [_ (error "unfamiliar type:" t)]))

;; handles parsing types like
;; (foo bar -> baz quux ~> xyzzy)
;; which is the same as
;; (foo -> (bar -> (baz ~> (quux ~> xyzzy))))
(define (parse-arrow-type t-arr args result-type)
  (match args
    [`(,as ... ~> ,(and (not '~> '->) bs) ...)
     (parse-arrow-type t-mono as (foldr t-arr result-type (map parse-type bs)))]
    [`(,as ... -> ,(and (not '~> '->) bs) ...)
     (parse-arrow-type t-fun as (foldr t-arr result-type (map parse-type bs)))]
    [`(,(not '~> '->) ...) (foldr t-arr result-type (map parse-type args))]))

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
;;;
;;; TODO: this code (and other code involving decls) is kind of complex. is
;;; there a simpler way?

;; A definition.
;; how is either 'any or 'mono
;; type is #f if no type signature provided.
(struct defn (name how type expr) #:transparent)

;; decls are used internally to produce defns, so we can separate type
;; annotations from declarations. we don't parse the expressions or types until
;; we turn them into defns.
;;
;; name is the variable being declared.
;; what is either 'tone, 'type, or 'expr.
;; if what is 'tone, value is either 'any or 'mono.
;; if what is 'type, value is a type (unparsed).
;; if what is 'expr, value is an expr (unparsed).
(struct decl (name what value) #:transparent)

;; produces a list of decls.
(define (parse-decl d)
  (define mono
    (match (car d)
      ['mono (set! d (cdr d)) #t]
      [_ #f]))
  (generate/list
   (define (yield-mono n) (yield (decl n 'tone 'mono)))
   (match d
     ;; just a monotone declaration
     [`(,(? ident? names) ...) #:when mono
      (for ([n names]) (yield-mono n))]
     ;; type declaration
     [`(,(? ident? names) ... : ,t)
      (for ([n names])
        (when mono (yield-mono n))
        (yield (decl n 'type t)))]
     ;; value declaration
     [`(,(? ident? name) ,(? ident? args) ... = . ,body)
      (set! body `(λ ,@args ,(parse-decl-body body)))
      (when mono (yield-mono name))
      (yield (decl name 'expr body))]
     [_ (error "could not parse decl:" d)])))

(define (parse-decl-body body)
  (match body
    [`(,expr) expr]
    [`(,expr where . ,decls) `(let ,decls ,expr)]))

;; produces a list of defns. for now, we don't support referring to a variable
;; before its definition, not even if you give it a type-signature. also, all
;; recursion must be explicit via `fix'.
(define (parse-decls ds Γ)
  (decls->defns (append* (map parse-decl ds)) Γ))

;; list of decls -> list of defns
(define (decls->defns ds Γ)
  (define type-sigs (make-hash))
  (define tone-sigs (make-hash))
  (begin0
    (for/generate/list ([d ds])
      (match d
        [(decl name 'tone k)
          (hash-set! tone-sigs name k)]
        [(decl name 'type t)
          (hash-set! type-sigs name (parse-type t))]
        [(decl name 'expr e)
          (define t (hash-ref type-sigs name #f))
          (define k (hash-ref tone-sigs name 'any))
          (yield (defn name k t (parse-expr e Γ)))
          (set! Γ (cons name Γ))
          (hash-remove! type-sigs name)
          (hash-remove! tone-sigs name)]))
    ;; if tone-sigs or type-sigs is non-empty, error.
    (for ([(k _) type-sigs])
      (error "type annotation for undefined variable:" k))
    (for ([(k _) tone-sigs])
      (error "tone annotation for undefined variable:" k))))

;; given some defns and an unparsed expr, parses the expr in the appropriate
;; environment and produces an expr which let-binds all the defns in the expr.
(define (parse-expr-letting defns e Γ)
  (set! e (parse-expr e (append (reverse (map defn-name defns)) Γ)))
  (for/fold ([e e]) ([d (reverse defns)])
    (match-define (defn n k t body) d)
    (e-let k n (if t (e-ann t body) body) e)))
