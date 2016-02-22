#lang racket

(require "util.rkt" "ast.rkt" "to-sexp.rkt")
(provide (all-defined-out))

(exception type-error)
(define (type-error-raw msg)
  (raise-type-error (string-append "TYPE ERROR\n" msg)))
(define (type-error fmt . args)
  (type-error-raw (apply format fmt args)))

;; type well-formedness
;; currently used only in contracts.
(define (type-wf? x)
  (match x
    [(t-base b) (base-type? b)]
    ;; functions that operate on types are generally not expected to handle
    ;; (t-name _); we substitute declared types for their referents as soon as
    ;; possible. so we consider (t-name _) not well-formed.
    [(t-name _) #f]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-record as) ((hash/c symbol? type-wf? #:immutable #t) as)]
    [(t-sum bs) ((hash/c symbol? (listof type-wf?) #:immutable #t) bs)]
    [(t-fun _ a b) (and (type-wf? a) (type-wf? b))]
    [(t-set a) (type-wf? a)]
    [(t-map k v) (and (type-wf? k) (eqtype? k) (type-wf? v))]
    ;; catch-all case, since we're used in contracts
    [_ (assert! (not (type? x))) #f]))

;; type equality is simple, but beware! because we have subtyping, testing for
;; type equality is not the same as testing for type *compatibility*.
(define/contract (type=? a b) (-> type-wf? type-wf? boolean?) (equal? a b))

;; However, there is no subtyping among equality types. So this is much safer to
;; use, if you know the types tested should be equality types.
(define (eqtype=? a b) (and (eqtype? a) (type=? a b)))


;; ========== Type Predicates ==========
(define/contract (lattice-type? x)
  (-> type-wf? boolean?)
  (match x
    [(or (t-base 'bool) (t-base 'nat) (t-set _)) #t]
    [(or (t-base 'str) (t-sum _)) #f]
    [(t-tuple ts) (andmap lattice-type? ts)]
    [(t-record as) (andmap lattice-type? (hash-values as))]
    [(t-map _ v) (lattice-type? v)]
    [(t-fun _ _ r) (lattice-type? r)]))

(define/contract (eqtype? x)
  (-> type-wf? boolean?)
  (match x
    [(t-base _) #t]
    [(t-tuple as)  (andmap eqtype? as)]
    [(t-record as) (andmap eqtype? (hash-values as))]
    [(t-sum as)    (andmap eqtype? (append* (hash-values as)))]
    [(t-fun _ _ _) #f]
    [(t-set a) (eqtype? a)]
    [(t-map k v) (assert! (eqtype? k)) (eqtype? v)]))

(define/contract (finite-type? t)
  (-> type-wf? boolean?)
  (match t
    [(t-base 'bool) #t]
    [(t-set a) (finite-type? a)]
    [(t-map k v) (and (finite-type? k) (finite-type? v))]
    [(t-tuple as)  (andmap finite-type? as)]
    [(t-record as) (andmap finite-type? (hash-values as))]
    [(t-sum as)    (andmap finite-type? (append* (hash-values as)))]
    [(t-fun _ a b) (andmap finite-type? (list a b))]
    [_ #f]))

(define (fixpoint-type? t)
  ;; for now this is all it takes. if we ever introduce lattice types which have
  ;; infinite descending chains, this'll get more complicated.
  ;;
  ;; also, functions of finite type should perhaps be allowed, but that's really
  ;; because they're secretly equality types. (TODO?)
  (and (lattice-type? t) (eqtype? t)))


;; ========== The type lattice ==========
(define/match (subtype? a b)
  [((t-tuple as) (t-tuple bs)) (map? subtype? as bs)]
  [((t-record as) (t-record bs))
   ;; records are invariant in their field-sets - adding fields does not produce
   ;; a subtype. this is because equality of records depends on what fields the
   ;; *actual* value has, so it's not parametric in the field-set. the
   ;; alternative is to make the meaning of equality type-indexed, and screw
   ;; that.
   (and (set=? (hash-keyset as) (hash-keyset bs))
        (for/and ([(field a) as]) (subtype? a (hash-ref bs field))))]
  [((t-sum as) (t-sum bs))
   (for/and ([(k vs) as])
     (and (hash-has-key? bs k)
          (map? subtype? vs (hash-ref bs k))))]
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
     #:when (set=? (hash-keyset as) (hash-keyset bs))
     (t-record (hash-intersection-with as bs lub))]
    [((t-sum as) (t-sum bs)) (t-sum (union as bs (curry unifys lub?)))]
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

;; two types are *compatible* iff they have a lub.
(define (type-compatible? a b)
  (with-handlers ([exn:type-error? (lambda (_) #f)])
    (type-lub a b)
    #t))


;; ========== The tone lattice ==========
;; any <: mono, any <: anti
(define (subtone? o1 o2) (equal? o2 (tone-unify #t o1 o2)))

(define/match (tone-unify lub? o p)
  [(_ x x) x]
  [(#f _ _) 'any]
  [(#t 'any x) x]
  [(#t x 'any) x]
  [(#t _ _) (type-error "tones have no lub: ~a, ~a" o p)])

(define/match (tone-inverse o)
  [('any) 'any]
  [('mono) 'anti]
  [('anti) 'mono]
  [(#f) #f])
