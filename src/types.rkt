#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

(struct exn:type-error exn:fail () #:transparent)

(define (type-error fmt . args)
  (define msg (string-append "TYPE ERROR\n" (apply format fmt args)))
  (raise (exn:type-error msg (current-continuation-marks))))

;; for now, type equality is simple
(define type=? equal?)

;; type well-formedness
(define (type-wf? x)
  (match x
    [(or (t-mono a b) (t-fun a b)) (and (type-wf? a) (type-wf? b))]
    [(t-fs a) (type-wf? a)]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-sum bs) ((hash/c symbol? type-wf? #:immutable #t) bs)]
    [(t-record as) ((hash/c symbol? type-wf? #:immutable #t) as)]
    [_ #t]))


;; Type "classes" or predicates
(define (lattice-type? x)
  (match x
    [(or (t-bool) (t-nat) (t-fs _)) #t]
    [(or (t-str) (t-sum _)) #f]
    [(t-tuple ts) (andmap lattice-type? ts)]
    [(t-record as) (andmap lattice-type? (hash-values as))]
    [(or (t-fun _ r) (t-mono _ r)) (lattice-type? r)]))

(define (eqtype? x)
  (match x
    [(or (t-bool) (t-nat) (t-str)) #t]
    [(or (t-record (app hash-values as)) (t-sum (app hash-values as))
         (t-tuple as))
     (andmap eqtype? as)]
    [(or (t-fun _ _) (t-mono _ _)) #f]
    [(t-fs a) (eqtype? a)]))

(define (finite-type? t)
  (match t
    [(t-bool) #t]
    [(t-fs a) (finite-type? a)]
    [(or (t-tuple as)
         (t-record (app hash-values as))
         (t-sum (app hash-values as)))
     (andmap finite-type? as)]
    [(or (t-fun a b) (t-mono a b)) (andmap finite-type? (list a b))]
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
  [((t-tuple as) (t-tuple bs)) (eqmap subtype? as bs)]
  [((t-record as) (t-record bs))
   ;; records are invariant in their field-sets - adding fields does not
   ;; preserve type. this is because equality of records depends on what fields
   ;; the *actual* value has, so it's not parametric in the field-set. the
   ;; alternative is to make the meaning of equality type-indexed, and screw
   ;; that.
   (and (set=? (hash-key-set as) (hash-key-set bs))
        (for/and ([(field a) as]) (subtype? a (hash-ref bs field))))]
  [((t-sum as) (t-sum bs))
    (for/and ([(k v) as])
      (and (hash-has-key? bs k) (subtype? v (hash-ref bs k))))]
  [((t-mono a x) (or (t-fun b y) (t-mono b y)))
    (and (subtype? b a) (subtype? x y))]
  [((t-mono a x) (t-mono b y))
    (and (subtype? b a) (subtype? x y))]
  [(x y) (type=? x y)])

(define/match (type-lub a b)
  [((t-tuple as) (t-tuple bs)) (t-tuple (type-lubs as bs))]
  [((t-record as) (t-record bs))
   #:when (set=? (hash-key-set as) (hash-key-set bs))
   (t-record (hash-intersection-with as bs type-lub))]
  [((t-sum as) (t-sum bs)) (t-sum (hash-union-with as bs type-lub))]
  [((t-mono a x) (t-mono b y))
    (t-mono (type-glb a b) (type-lub x y))]
  [((or (t-mono a x) (t-fun a x)) (or (t-mono b y) (t-fun b y)))
    (t-fun (type-glb a b) (type-lub x y))]
  [((t-fs a) (t-fs b)) (t-fs (type-lub a b))]
  [(x y) #:when (type=? x y) x]
  [(x y) (type-error "no lub: ~v and ~v" x y)])

(define/match (type-glb a b)
  [((t-tuple as) (t-tuple bs)) (t-tuple (type-glbs as bs))]
  [((t-record as) (t-record bs))
   #:when (set=? (hash-key-set as) (hash-key-set bs))
   (t-record (hash-union-with as bs type-glb))]
  [((t-sum as) (t-sum bs)) (t-sum (hash-intersection-with as bs type-glb))]
  [((t-fun a x) (t-fun b y))
    (t-fun (type-lub a b) (type-glb x y))]
  [((or (t-mono a x) (t-fun a x)) (or (t-mono b y) (t-fun b y)))
    (t-mono (type-lub a b) (type-glb x y))]
  [((t-fs a) (t-fs b)) (t-fs (type-glb a b))]
  [(x y) #:when (type=? x y) x]
  [(x y) (type-error "no glb: ~v and ~v" x y)])

(define (type-lubs as bs)
  (unless (= (length as) (length bs)) (type-error "lists of unequal length"))
  (map type-lub as bs))

(define (type-glbs as bs)
  (unless (= (length as) (length bs)) (type-error "lists of unequal length"))
  (map type-glb as bs))
