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

;; TODO: Do I ever use type-map and type-fold?
(define (type-map f t)
  (parametric->/c [X Y]
    (-> (-> X Y) (type-over X) (type-over Y)))
  (match t
    [(or `(var ,_) (? base-type?)) t]
    [`(,(and form (or 'box '-> '* 'set)) ,@as) `(,form ,@(map f as))]
    [`(+ ,h) `(+ ,(hash-map-vals f h))]))

(define (type-fold t f)
  (f (type-map (lambda (x) (type-fold x f)) t)))

(define-flat-contract type? (type-over type?))

;; only exact types without free type variables can be lattice types.
(define-flat-contract semilattice-type?
  'bool
  (list/c '-> type? semilattice-type?)
  (cons/c '* (listof semilattice-type?))
  (list/c 'set type?))

;; TODO: put actual restrictions on fixed points here.
(define-flat-contract fixpoint-type? semilattice-type?)
