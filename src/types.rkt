#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt")
(provide (all-defined-out))

(struct exn:type-error exn:fail () #:transparent)

(define (type-error fmt . args) (type-error-raw (apply format fmt args)))
(define (type-error-raw msg)
  (raise (exn:type-error (string-append "TYPE ERROR\n" msg)
                         (current-continuation-marks))))

;; type equality is simple, but beware! because we have subtyping, testing for
;; type equality is not the same as testing for type *compatibility*.
(define type=? equal?)

;; However, there is no subtyping among equality types. So this is much safer to
;; use, if you know the types tested should be equality types.
(define (eqtype=? a b) (and (eqtype? a) (type=? a b)))

;; type well-formedness
;; NB. currently unused.
(define (type-wf? x)
  (match x
    [(t-fun _ a b) (and (type-wf? a) (type-wf? b))]
    [(t-set a) (type-wf? a)]
    [(t-map k v) (and (type-wf? k) (eqtype? k) (type-wf? v))]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-sum bs) ((hash/c symbol? type-wf? #:immutable #t) bs)]
    [(t-record as) ((hash/c symbol? type-wf? #:immutable #t) as)]
    [_ #t]))

;; TODO: better names
(define (type-unify a b)
  (unless (type=? a b)
    (type-error "unequal types: ~s, ~s" (type->sexp a) (type->sexp b)))
  a)

(define (types-unify as)
  (assert! (not (null? as)))
  (for/fold ([a (first as)]) ([b (rest as)])
    (type-unify a b)))


;; ========== Type Predicates ==========
(define/match (lattice-type? x)
  [((or (t-base 'bool) (t-base 'nat) (t-set _))) #t]
  [((or (t-base 'str) (t-sum _))) #f]
  [((t-tuple ts)) (andmap lattice-type? ts)]
  [((t-record as)) (andmap lattice-type? (hash-values as))]
  [((t-map _ v)) (lattice-type? v)]
  [((t-fun _ _ r)) (lattice-type? r)])

(define/match (eqtype? x)
  [((t-base _)) #t]
  [((t-fun _ _ _)) #f]
  [((t-tuple as)) (andmap eqtype? as)]
  [((or (t-record as) (t-sum as))) (andmap eqtype? (hash-values as))]
  [((t-set a)) (eqtype? a)]
  [((t-map k v)) (assert! (eqtype? k)) (eqtype? v)])

(define/match (finite-type? t)
  [((t-base 'bool)) #t]
  [((t-set a)) (finite-type? a)]
  [((t-map k v)) (and (finite-type? k) (finite-type? v))]
  [((t-tuple as)) (andmap finite-type? as)]
  [((or (t-record as) (t-sum as))) (andmap finite-type? (hash-values as))]
  [((t-fun _ a b)) (andmap finite-type? (list a b))]
  [(_) #f])

;; for now this is all it takes. if we ever introduce lattice types which have
;; infinite descending chains, this'll get more complicated.
;;
;; also, functions of finite type should perhaps be allowed, but that's really
;; because they're secretly equality types. (TODO?)
(define fixpoint-type? (and/c lattice-type? eqtype?))
