#lang racket

(require "util.rkt" syntax/parse/define)
(provide (all-defined-out))

;; Whether a variable/hypothesis, function, etc. is unrestricted or monotone.
;; TODO: antitone?
(define-flat-contract tone? 'disc 'mono)
(define-flat-contract base-type? 'bool 'nat 'str)

;; ---------- Types ----------
(define (type-over type?)
  (or/c
   base-type?
   (list/c 'var symbol?) ;; type variables or named types
   (list/c 'box type?)   ;; discrete comonad
   (list/c '-> type? type?)
   ;; product & sum types
   (cons/c '* (listof type?))
   (list/c '+ (hash/c symbol? type? #:immutable #t))
   (list/c 'set type?)))

(define (type-map f t)
  (parametric->/c [X Y]
    (-> (-> X Y) (type-over X) (type-over Y)))
  (match t
    [(or '_ `(var ,_) (? base-type?)) t]
    [`(,(and form (or 'box '-> '* 'set)) ,@as) `(,form ,@(map f as))]
    [`(+ ,h) `(+ ,(hash-map-vals f h))]))

(define (type-fold t f)
  (f (type-map (lambda (x) (type-fold x f)) t)))

(define-flat-contract exact-type? (type-over exact-type?))
(define-flat-contract fuzzy-type? '_ (type-over fuzzy-type?))

;; only exact types without free type variables can be lattice types.
(define-flat-contract semilattice-type?
  'bool
  (list/c '-> exact-type? semilattice-type?)
  (cons/c '* (listof semilattice-type?))
  (list/c 'set exact-type?))

;; TODO: put actual restrictions on fixed points here.
(define-flat-contract fixpoint-type? semilattice-type?)


;; Merges two fuzzy types, if they're compatible. Otherwise, errors.
;; If any argument is exact, the result will be exact and equal to the argument[*],
;; or else an exception will be thrown.
;;
;; [*] It's hard to express this property using Racket contracts (I tried using
;; and/c, but and/c doesn't actually act like an intersection type - it just
;; applies all the contracts in order). I could probably use a dependent
;; contract, but meh.
(define/contract (fuzzy-type-merge A B)
  (-> fuzzy-type? fuzzy-type? fuzzy-type?)
  (match* (A B)
    [(A B) #:when (eq? A B) A]
    [(A '_) A]
    [('_ B) B]
    ;; most type forms just take a list of types as arguments
    [(`(,(and form (or '-> '* 'set 'box)) ,@as) `(,form2 ,@bs))
     #:when (and (eq? form form2) (length=? as bs))
     `(,form ,@(map fuzzy-type-merge as bs))]
    [(`(+ ,h1) `(+ ,h2))
     ;; sums must have *same* sets of tags. fuzzy type merging has nothing to do
     ;; with subtyping!
     #:when (equal? (hash-keyset h1) (hash-keyset h2))
     `(+ ,(hash-map-vals fuzzy-type-merge h1 h2))]
    ;; TODO: good error messages
    [(_ _) (error (format "cannot unify ~s with ~s" A B))]))
