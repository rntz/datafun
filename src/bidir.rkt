#lang racket

(require "util.rkt" "abt.rkt")
(provide (all-defined-out))

;;; simple vaguely Datafun-like language w/ polymorphism & bidirectional type
;;; inference.
;;;
;;; Datafun features we include:
;;; - tonicity
;;; - kinds and subkinding
;;; - subtyping (based on tonicity & subkinding)

(define tone? (or/c 'any 'mono))
(define kind? (or/c 'type 'lattice))
(define base-type? (or/c 'nat 'str))

;; # EXPRESSIONS
(enum expr
  (e-var name)
  ;; TODO: e-prim for primitives
  (e-lit lit)
  (e-lam var body)
  (e-app func arg)
  (e-ann type expr))

;; # TYPES
;;
;; types are represented using ABT from abt.rkt. we define a language of type
;; formers for use with this ABT representation.
(define-syntax-rule (enum/c (name arg/c ...) ...)
  (or/c (list/c 'name arg/c ...) ...))

(define type-former?
  (enum/c
   (exvar symbol?)
   (base base-type?)
   (tuple exact-nonnegative-integer?)
   (fun tone?)
   (univ kind?)))

;; just checks arity-correctness.
(define (type-wf? t)
  (match (view t)
    [(Var _ _) #t]
    [(App form args)
     (and (type-former? form)
          (map? type-binder-wf? args (arity form)))]))

(define (type-binder-wf? A num-vars)
  (matches? A (binder (app length (== num-vars =)) (? type-wf?))))

(define/contract (arity f)
  (-> type-former? (listof exact-nonnegative-integer?))
  (match f
    [(or `(exvar ,_) `(base ,_)) (list)]
    [`(tuple ,n) (for/list ([_ n]) 0)]
    [`(fun ,_) (list 0 0)]
    [`(univ ,k) (list 1)]))


;;; Conveniences for constructing/deconstructing types

;; when your match expander and your expression expander are the same,
;; define-match-iso avoids repetition.
(define-syntax-rule (define-match-iso name e)
  (define-match-expander name e e))

(define-match-iso t-exvar (syntax-rules () [(_ id) (App `(exvar ,id) '())]))
(define-match-iso t-base  (syntax-rules () [(_ t)  (App `(base ,t) '())]))

(define (make-t-tuple . as) (App `(tuple ,(length as)) as))
(define-match-expander t-tuple
  (syntax-parser [(_ a ...) #'(App `(tuple ,_) (list a ...))])
  ;; ;; would like to do this, but get strange errors, see
  ;; ;; http://bugs.racket-lang.org/query/?cmd=view&pr=15223
  ;; (make-rename-transformer #'t-tuple)
  (syntax-parser [(_ a ...) #'(make-t-tuple a ...)]))

(define-match-iso t-fun
  (syntax-rules () [(_ tone a b) (App `(fun ,tone) (list a b))]))


;; Typechecking environments.
(define the-env (make-parameter #f))

;; exprs: hash from expression variable symbols to expr-infos.
;; types: list of kinds of universal type vars.
;; exvars: hash from exvar identifier symbols to kinds.
(struct env (exprs types exvars) #:transparent)
(struct expr-info (tone type) #:transparent)

(define (expr-var-info name)
  (hash-ref (env-exprs (the-env)) name
            (lambda () (error "no such expression variable: " name))))

(define (type-var-kind index)
  (list-ref (env-types (the-env)) index))

(define (exvar-kind name)
  (hash-ref (env-exvars (the-env)) name
            (lambda () (error "no such exvar: " name))))

(define/contract (env-bind-expr e name tone type)
  (env? symbol? tone? type-wf? . -> . env?)
  ;; TODO: check type is wf in e.
  (match-define (env exprs types exvars) e)
  (env (hash-set exprs name (expr-info tone type)) types exvars))

(define/contract (env-bind-univ e kind)
  (env? kind? . -> . env?)
  (match-define (env exprs types exvars) e)
  (env exprs (cons kind types) exvars))

(define/contract (env-bind-exvar e id kind)
  (env? symbol? kind? . -> . env?)
  (match-define (env exprs types exvars) e)
  (env exprs types (hash-set exvars id kind)))


;; Ctxs map exvars to their types.
(define the-ctx (make-parameter #f))

;; FUCK: this won't work, needs to be *ordered*
;; see InstLReach, page 7
(define ctx? (hash/c symbol? type-wf? #:immutable #t))
(define (ctx-union a b)
  (hash-union-with a b (lambda (_a _b) (error "exvar already has type"))))
(define (ctx-restrict ctx)
  (hash-select-keys ctx (hash-key-set (env-exvars (the-env)))))
(define (ctx-restrict!) (the-ctx (ctx-restrict (the-ctx))))

(define (exvar-type id) (hash-ref (the-ctx) id #f))
(define (concretize-type ctx type) TODO)


;;; Syntax conveniences
(define-syntax-rule (with-var name tone type body ...)
  (parameters ([the-env (env-bind-expr (the-env) name tone type)]) body ...))

(define-syntax-rule (with-univ kind body ...)
  (parameterize ([the-env (env-bind-univ (the-env) kind)]) body ...))

(define-syntax-rule (with-exvar name kind body ...)
  (let ([name (gensym '?)])
    (begin0
        (parameterize ([the-env (env-bind-exvar (the-env) name kind)])
          body ...)
      (ctx-restrict!))))


;;; Simple type operations
;; any <: mono
(define/match (tone-lub o1 o2)
  [('any 'any) 'any]
  [(_ _) 'mono])

;; lattice <: type
(define/match (kind-lub k1 k2)
  [('lattice 'lattice) 'lattice]
  [(_ _) 'type])

(define (subtone? o p) (equal? (tone-lub o p) p))
(define (subkind? k l) (equal? (kind-lub k l) l))

(define (monotype? t)
  (match (view t)
    [(Var _ _) #t]
    [(t-exvar _) #t]
    [(t-base _) #t]
    [(t-tuple ts ...) (andmap monotype? ts)]
    [(t-fun _ a b) (andmap monotype? (list a b))]
    [(App `(univ ,_) _) #f]))

;; we can only ask the kind of a monotype.
(define/contract (kind t)
  (-> (and/c type-wf? monotype?) kind?)
  (match (view t)
    [(Var i _) (type-var-kind i)]
    [(t-exvar n) (exvar-kind n)]
    [(t-base 'nat) 'lattice]
    [(t-base 'str) 'type]
    [(t-tuple ts ...) (foldl kind-lub 'lattice (map kind ts))]
    [(t-fun _ _ b) (kind b)]))


;;; Subtyping. Mutates the ctx.
(define/contract (subtype! a b)
  (-> type-wf? type-wf? void?)
  (match* ((view a) (view b))
    [((Var i _) (Var i _)) (void)]
    ;; TODO: exvar, base
    [((t-exvar a) (t-exvar b))
     TODO]
    [((t-base a) (t-base b))
     (unless (equal? a b)
       (error "base types are not subtypes of one another"))]
    [((t-tuple as ...) (t-tuple bs ...))
     (unless (length=? as bs)
       (error "tuples have different lengths"))
     (void (map subtype! as bs))]
    [((t-fun o a x) (t-fun p b y))
     (unless (subtone? o p)
       (error "cannot subtype functions, wrong tones"))
     (subtype! x y)
     (subtype! b a)]
    [(_ (App `(univ ,k) (binder (list _) b)))
     (with-univ k
       (subtype! (Subst a (Shift 1)) b))]
    ;; existential variable introduction
    [((App `(univ ,k) A) _)
     (with-exvar ax k
       (subtype! (bind A (list (t-exvar ax))) b))]
    [(_ _)
     (error "I'm sorry Dave, I can't do that")]))
