#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

(define (type-error fmt . args)
  (error (apply format (string-append "type error: " fmt) args)))


;; Type utilities.
(define/match (subtype? a b)
  [((t-tuple as) (t-tuple bs)) (eqmap subtype? as bs)]
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
  [((t-sum as) (t-sum bs)) (t-sum (hash-intersection-with as bs type-lub))]
  [((t-mono a x) (t-mono b y))
    (t-mono (type-glb a b) (type-lub x y))]
  [((or (t-mono a x) (t-fun a x)) (or (t-mono b y) (t-fun b y)))
    (t-fun (type-glb a b) (type-lub x y))]
  [((t-fs a) (t-fs b)) (t-fs (type-lub a b))]
  [(x y) #:when (type=? x y) x]
  [(x y) (type-error "no lub: ~a and ~a" x y)])

(define/match (type-glb a b)
  [((t-tuple as) (t-tuple bs)) (t-tuple (type-glbs as bs))]
  [((t-sum as) (t-sum bs)) (t-sum (hash-union-with as bs type-glb))]
  [((t-fun a x) (t-fun b y))
    (t-fun (type-lub a b) (type-glb x y))]
  [((or (t-mono a x) (t-fun a x)) (or (t-mono b y) (t-fun b y)))
    (t-mono (type-lub a b) (type-glb x y))]
  [((t-fs a) (t-fs b)) (t-fs (type-glb a b))]
  [(x y) #:when (type=? x y) x]
  [(x y) (type-error "no glb: ~a and ~a" x y)])

(define (type-lubs as bs)
  (unless (= (length as) (length bs)) (type-error "lists of unequal length"))
  (map type-lub as bs))

(define (type-glbs as bs)
  (unless (= (length as) (length bs)) (type-error "lists of unequal length"))
  (map type-glb as bs))


;; an env is a list of hyp(othese)s. h-any is an unrestricted hyp; h-mono is a
;; monotone hyp; h-hidden is a monotone hyp hidden by entry into a constant
;; expression (e.g. argument to a non-monotone function).
(enum hyp (h-any type) (h-mono type) (h-hidden))
(define env? (listof h-any?))

(define env-cons cons)
(define env-ref list-ref)
(define (env-extend extension env) (append (reverse extension) env))

(define (env-hide-mono Γ)
  (map (match-lambda [(h-mono _) (h-hidden)] [x x]) Γ))

;; Elaborated expression forms:
;; e-app-{fun,mono} distinguish applying functions from monotone functions
(struct e-app-fun e-app () #:transparent)
(struct e-app-mono e-app () #:transparent)


;;; Synthesis & checking.
;; returns two values: type & elaborated expression.
(define (elab-synth Γ e)
  (define (ok t) (values t e))
  (match e
    [(e-ann t e) (values t (e-ann t (elab-check Γ t e)))]
    [(e-var n i)
      (match (env-ref Γ i)
        [(or (h-any t) (h-mono t)) (ok t)]
        [_ (type-error "hidden variable: ~a" n)])]
    [(e-lit v) (ok (lit-type v))]
    [(e-prim p)
      (define t (prim-type-synth p))
      (if t (ok t)
        (type-error "can't infer type of primitive: ~a" p))]
    [(e-app f a)
      (define-values (ft f) (elab-synth Γ f))
      (match ft
        [(-> i o) (values o (e-app-mono f (elab-check (env-hide-mono Γ) i a)))]
        [(~> i o) (values o (e-app-fun f (elab-check Γ i a)))]
        [_ (type-error "applying non-function ~a, of type ~a" f ft)])]
    [(e-proj i subj)
      (define-values (subjt subj) (elab-synth Γ subj))
      (match subjt
        [(t-tuple ts) #:when (< i (length ts))
          (values (list-ref ts i) (e-proj i subj))]
        [(t-tuple _) (type-error "projection index out of bounds")]
        [_ (type-error "projecting from non-tuple ~a, which has type ~a"
             subj subjt)])]
    ;; TODO: synthesize case, let-in, and join expressions when possible, even
    ;; though it's non-standard.
    ;;
    ;; NB. technically I shouldn't be synthesizing tuples, tagged values, or
    ;; singleton sets, since they're introduction forms. but w/e.
    [(e-tuple as)
      (define-values (ts es)
        (for/lists (ts es) ([a as]) (elab-synth Γ a)))
      (values (t-tuple ts) (e-tuple es))]
    [(e-tag name subj)
      (define-values (subjt subj) (elab-synth Γ subj))
      (values (Σ (name subjt)) (e-tag name subj))]
    [(e-singleton subj)
      (define-values (subjt subj) (elab-synth Γ subj))
      (values (FS subjt) (e-singleton subj))]
    [(or (e-fun _ _) (e-mono _ _) (e-fix _ _) (e-empty) (e-join _ _)
       (e-case _ _) (e-letin _ _ _))
      (type-error "can't infer type of: ~a" e)]))

;; returns elaborated expression.
(define (elab-check Γ t e)
  (match e
    [(e-ann st s)
      (unless (subtype? st t) (type-error "incompatible types: ~a and ~a" t st))
      (e-ann st (elab-check Γ st s))]
    ))
