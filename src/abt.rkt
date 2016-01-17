#lang racket

(require "util.rkt")
(provide (all-defined-out))

;; ---------- EXPLICIT SUBSTITUTIONS ----------
;; see "Explicit Substitutions"; Abadi, Cardelli, Curien, Levy; 1996
;; using lazy evaluation is my idea, but no doubt others have had it as well

;; subst variable names: s, t, u
;;
;; TODO?: would hash-consing improve efficiency here?
(enum subst
  (Shift n)
  (Cons a s)
  (Compose s t))

(define id-subst (Shift 0))

(define (subst-whnf? s)
  (matches? s (or (Shift _) (Cons _ _))))

(define (subst-ref s i [name #f])
  (match (subst-shift i s)
    [(Cons a _) a]
    [(Shift j) (Var j name)]))


;;; ---------- NORMALIZING SUBSTITUTIONS ----------
;; maps substitutions to their evaluations. is a parameter "just in case";
;; usually (since it's weak) you shouldn't have to touch this.
(define subst-whnf-memo (make-parameter (make-weak-hasheq)))

(define/contract (subst-whnf s)
  (-> subst? subst-whnf?)
  (match s
    [(Compose a b)
     (hash-ref! (subst-whnf-memo) s (lambda () (subst-compose a b)))]
    [(or (Shift _) (Cons _ _)) s]))

(define/contract (subst-compose s t)
  (-> subst? subst? subst-whnf?)
  (match s
    [(Shift n) (subst-shift n t)]
    [(Cons a s) (Cons (Subst a t) (Compose s t))]
    [(Compose s1 s2) (subst-compose s1 (Compose s2 t))]))

(define/contract (subst-shift n s)
  (-> exact-nonnegative-integer? subst? subst-whnf?)
  (match* (n (subst-whnf s))
    [(0 s) s]
    [(n (Shift m)) (Shift (+ n m))]
    [(n (Cons a s)) (subst-shift (- n 1) s)]))


;;; ---------- TERM AND BINDER STRUCTURE ----------
;; term variable names: a, b, c
(enum term
  ;; "name" is purely for annotation purposes. it can be used for any annotation
  ;; you like, but usually for a human-readable variable name. by convention, #f
  ;; means "no annotation" (or "unknown name").
  (Var index name)
  ;; an application of a form to a list of arguments.
  ;; the form is a symbol, usually.
  ;; the arguments are binders.
  (App form args)
  ;; applies a substitution to a term.
  (Subst term subst))

;; binder variable names: A, B, C
;;
;; A binder is an improper list of variable names (symbols), the tail of which
;; is a term. For example, ('x 'y . (Var 1 'x)) represents (x,y. x).
(define binder? (flat-rec-contract binder? term? (cons/c symbol? binder?)))
(define-match-expander binder
  (syntax-parser [(_ vars term)
                  #'(app improper-list->pair
                         (cons (and vars (list (? symbol?) (... ...)))
                               (? term? term)))])
  (syntax-parser [(_ vars term) #'(foldr cons term vars)]))

(define (improper-list->pair l)
  (let loop ([acc '()] [l l])
    (if (pair? l) (loop (cons (car l) acc) (cdr l))
        (cons (reverse acc) l))))


;;; ---------- SUBSTITUTION OPERATIONS PROPER ----------
;; binds/substitutes-for all variables in a binder, yielding a term
(define/contract (bind A terms)
  (-> binder? (listof term?) term?)
  (match-define (binder vars a) A)
  (assert! (length=? vars terms))
  (bind-in-term a terms))

;; using this directly forgoes check that we're substituting the right # of
;; variables.
(define/contract (bind-in-term a terms)
  (-> term? (listof term?) term?)
  (Subst a (foldr Cons id-subst terms)))

(define (subst-under-binder vars s)
  (define n (length vars))
  (foldr Cons (Compose s (Shift n))
         (map Var (sequence->list n) vars)))

;; Shallowly views a term or binder in a subst, returning a Var, App, or binder
;; (but never a Subst).
(define (view a [s id-subst])
  (match a
    [(Subst b t) (view b (Compose t s))]
    ;; this is not merely an optimization.
    ;; it's necessary for the case after it to work.
    [a #:when (eq? s id-subst) a]
    [(Var index name) (view (subst-ref s index name) id-subst)]
    [(App form args)
     (App form (map (lambda (A) (view A s)) args))]
    [(binder vars term)
     (binder vars (Subst term (subst-under-binder vars s)))]))

;; eliminates all instances of Subst from a term or binder.
(define (deep-view a [s id-subst])
  (match a
    [(Subst b t) (deep-view b (Compose t s))]
    [(Var _ _) #:when (eq? s id-subst) a]
    [(Var index name) (deep-view (subst-ref s index name) id-subst)]
    [(App form args) (App form (map (lambda (A) (deep-view A s)) args))]
    [(binder vars term)
     (binder vars (deep-view term (subst-under-binder vars s)))]))
