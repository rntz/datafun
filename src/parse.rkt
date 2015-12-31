#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.
;; TODO: an exception class for parse failures.

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
     (set! e (parse-expr e (rev-append xs Γ)))
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
          (set! e (parse-expr e (rev-append (pat-vars p) Γ)))
          (case-branch p e)))]
    [`(join . ,es) (e-join (map r es))]
    [`(set . ,es) (e-set (map r es))]
    [`(let ,decls ,body)
     (parse-expr-letting (parse-all-decls decls Γ) body Γ)]
    [`(,expr where . ,decls)
     (parse-expr-letting (parse-all-decls decls Γ) expr Γ)]
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

;; A definition.
;; tone is either 'any or 'mono
;; type is #f if no type signature provided.
(struct defn (name tone type expr) #:transparent)

(struct decl-state (tone-sigs type-sigs) #:transparent)

(define empty-decl-state (decl-state (hash) (hash)))

(define (parse-all-decls ds Γ)
  (define-values (new-state defns) (parse-decls empty-decl-state ds Γ))
  (match-define (decl-state tone-sigs type-sigs) new-state)
  (for ([(n _) type-sigs])
    (error "type ascription for undefined variable:" n))
  (for ([(n _) tone-sigs])
    (error "monotonicity declaration for undefined variable:" n))
  defns)

;; returns (values new-state list-of-defns), or errors
;;
;; for now, we don't support referring to a variable before its definition, not
;; even if you give it a type-signature. also, all recursion must be explicit
;; via `fix'.
(define (parse-decls state ds Γ)
  ;; (printf "parse-decls ~a\n" ds)
  (define defns '())
  (for ([d ds])
    ;; (printf "parsing ~a\n" d)
    (define-values (new-state new-defns) (parse-decl state d Γ))
    (set! state new-state)
    (set! Γ (rev-append (map defn-name new-defns) Γ))
    (set! defns (rev-append new-defns defns)))
  (values state (reverse defns)))

;; returns (values new-state list-of-defns), or errors
(define (parse-decl state d Γ)
  ;; (printf "parse-decl ~a\n" d)
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
    [`(,(? ident? names) ... : ,t)
     (define type (parse-type t))
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
     (ret (list (defn name tone type (parse-expr expr Γ))))]
    [_ (error "could not parse declaration:" d)]))

;; given some defns and an unparsed expr, parses the expr in the appropriate
;; environment and produces an expr which let-binds all the defns in the expr.
(define (parse-expr-letting defns e Γ)
  (set! e (parse-expr e (rev-append (map defn-name defns) Γ)))
  (for/fold ([e e]) ([d (reverse defns)])
    (match-define (defn n k t body) d)
    (e-let k n (if t (e-ann t body) body) e)))
