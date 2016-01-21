#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt")
(provide (all-defined-out))

(struct exn:type-error exn:fail () #:transparent)

(define (type-error fmt . args) (type-error-raw (apply format fmt args)))
(define (type-error-raw msg)
  (raise (exn:type-error (string-append "TYPE ERROR\n" msg)
                         (current-continuation-marks))))

;; for now, type equality is simple
(define type=? equal?)

;; type well-formedness
;; NB. currently unused.
(define (type-wf? x)
  (match x
    [(t-fun _ a b) (and (type-wf? a) (type-wf? b))]
    [(t-set a) (type-wf? a)]
    [(t-map k v) (and (type-wf? k) (type-wf? v) (eqtype? k))]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-sum bs) ((hash/c symbol? type-wf? #:immutable #t) bs)]
    [(t-record as) ((hash/c symbol? type-wf? #:immutable #t) as)]
    [_ #t]))


;; Type "classes" or predicates
(define (lattice-type? x)
  (match x
    [(or (t-base 'bool) (t-base 'nat) (t-set _)) #t]
    [(or (t-base 'str) (t-sum _)) #f]
    [(t-tuple ts) (andmap lattice-type? ts)]
    [(t-record as) (andmap lattice-type? (hash-values as))]
    [(t-map _ v) (lattice-type? v)]
    [(t-fun _ _ r) (lattice-type? r)]))

(define (eqtype? x)
  (match x
    [(t-base _) #t]
    [(or (t-record (app hash-values as)) (t-sum (app hash-values as))
         (t-tuple as))
     (andmap eqtype? as)]
    [(t-fun _ _ _) #f]
    [(t-set a) (eqtype? a)]
    [(t-map k v) (assert! (eqtype? k)) (eqtype? v)]))

(define (finite-type? t)
  (match t
    [(t-base 'bool) #t]
    [(t-set a) (finite-type? a)]
    [(t-map k v) (and (finite-type? k) (finite-type? v))]
    [(or (t-tuple as)
         (t-record (app hash-values as))
         (t-sum (app hash-values as)))
     (andmap finite-type? as)]
    [(t-fun _ a b) (andmap finite-type? (list a b))]
    [_ #f]))

(define (fixpoint-type? t)
  ;; for now this is all it takes. if we ever introduce lattice types which have
  ;; infinite descending chains, this'll get more complicated.
  ;;
  ;; also, functions of finite type should perhaps be allowed, but that's really
  ;; because they're secretly equality types. (TODO?)
  (and (lattice-type? t) (eqtype? t)))


;; Subtyping & the type lattice.
(define/match (subtype? a b)
  [((t-tuple as) (t-tuple bs)) (map? subtype? as bs)]
  [((t-record as) (t-record bs))
   ;; records are invariant in their field-sets - adding fields does not produce
   ;; a subtype. this is because equality of records depends on what fields the
   ;; *actual* value has, so it's not parametric in the field-set. the
   ;; alternative is to make the meaning of equality type-indexed, and screw
   ;; that.
   (and (set=? (hash-key-set as) (hash-key-set bs))
        (for/and ([(field a) as]) (subtype? a (hash-ref bs field))))]
  [((t-sum as) (t-sum bs))
    (for/and ([(k v) as])
      (and (hash-has-key? bs k) (subtype? v (hash-ref bs k))))]
  [((t-fun o1 a1 b1) (t-fun o2 a2 b2))
   ;; the reversal of o1 and o2 in the call to subtype? is deliberate
   (and (subtone? o2 o1) (subtype? a2 a1) (subtype? b1 b2))]
  [((t-set a) (t-set b)) (subtype? a b)]
  [((t-map a x) (t-map b y)) (and (subtype? a b) (subtype? x y))]
  [(x y) (type=? x y)])

;; `lub' is a boolean. If #t, we find the least upper bound of types `a' and
;; `b', if it exists. If #f, we find their greatest lower bound, if it exists.
(define (unify lub? a b)
  (define glb? (not lub?))
  (define lub (curry unify lub?))
  (define glb (curry unify glb?))
  (define union (if lub? hash-union-with hash-intersection-with))
  (match* (a b)
    [((t-tuple as) (t-tuple bs)) (t-tuple (unifys lub? as bs))]
    [((t-record as) (t-record bs))
     #:when (set=? (hash-key-set as) (hash-key-set bs))
     (t-record (hash-intersection-with as bs lub))]
    [((t-sum as) (t-sum bs)) (t-sum (union as bs lub))]
    [((t-fun o a x) (t-fun p b y))
     (t-fun (tone-unify (not lub?) o p) (glb a b) (lub x y))]
    [((t-set a) (t-set b)) (t-set (lub a b))]
    [((t-map a x) (t-map b y)) (t-map (lub a b) (lub x y))]
    [(x y) #:when (type=? x y) x]
    [(x y) (type-error "no ~a: ~s and ~s" (if lub? 'lub 'glb)
                       (type->sexp x) (type->sexp y))]))

(define type-lub (curry unify #t))
(define type-glb (curry unify #f))
(define (unifys lub? as bs)
  (unless (length=? as bs) (type-error "lists of unequal length"))
  (map (curry unify lub?) as bs))

;; any <: mono, any <: anti
(define (subtone? o1 o2) (equal? o2 (tone-unify #t o1 o2)))
(define/match (tone-unify lub? o p)
  [(_ x x) x]
  [(#f _ _) 'any]
  [(#t 'any x) x]
  [(#t x 'any) x]
  [(#t _ _) (type-error "tones have no lub: ~a, ~a" o p)])
