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
  [(x y) (type-error "no lub: ~v and ~v" x y)])

(define/match (type-glb a b)
  [((t-tuple as) (t-tuple bs)) (t-tuple (type-glbs as bs))]
  [((t-sum as) (t-sum bs)) (t-sum (hash-union-with as bs type-glb))]
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


;;; Inference & checking.
;; returns two values: type & elaborated expression.
(define (elab-infer Γ e)
  (define (ok t) (values t e))
  (match e
    [(e-ann t e) (values t (e-ann t (elab-check Γ t e)))]
    [(e-lit v) (ok (lit-type v))]

    [(e-var n i)
      (match (env-ref Γ i)
        [(or (h-any t) (h-mono t)) (ok t)]
        [_ (type-error "hidden variable: ~a" n)])]

    [(e-prim p)
      (define t (prim-type-infer p))
      (if t (ok t)
        (type-error "can't infer type of primitive: ~a" p))]

    [(e-app f a)
      (define-values (ft fe) (elab-infer Γ f))
      (match ft
        [(~> i o) (values o (e-app-mono fe (elab-check (env-hide-mono Γ) i a)))]
        [(-> i o) (values o (e-app-fun fe (elab-check Γ i a)))]
        [_ (type-error "applying non-function ~v, of type ~v" f ft)])]

    [(e-proj i subj)
      (define-values (subj-t subj-e) (elab-infer Γ subj))
      (match subj-t
        [(t-tuple ts) #:when (< i (length ts))
          (values (list-ref ts i) (e-proj i subj-e))]
        [(t-tuple _) (type-error "projection index out of bounds")]
        [_ (type-error "projecting from non-tuple ~v, which has type ~v"
             subj-e subj-t)])]

    ;; TODO: synthesize let-in and join expressions when possible, even though
    ;; it's non-standard.
    ;;
    ;; NB. technically I shouldn't be synthesizing tuples, tagged values, or
    ;; singleton sets, since they're introduction forms. but w/e.
    [(e-tuple as)
      (define-values (ts es)
        (for/lists (ts es) ([a as]) (elab-infer Γ a)))
      (values (t-tuple ts) (e-tuple es))]

    [(e-tag name subj)
      (define-values (subj-t subj-e) (elab-infer Γ subj))
      (values (Σ (name subj-t)) (e-tag name subj-e))]

    [(e-singleton subj)
      (define-values (subj-t subj-e) (elab-infer Γ subj))
      (values (FS subj-t) (e-singleton subj-e))]

    [(e-case subj branches)
      (when (null? branches)
        (type-error "can't infer type of case with no branches"))
      (define-values (subj-t subj-e) (elab-infer (env-hide-mono Γ) subj))
      (define-values (branch-ts branch-es)
        (for/lists (_ts _es) ([b branches])
          (match-define (case-branch pat body) b)
          ;; it's okay to use h-any here ONLY because we hid the monotone
          ;; environment when checking subj.
          (define pat-Γ (map h-any (check-pat Γ subj-t pat)))
          (define-values (branch-t branch-e) (elab-infer (append pat-Γ Γ) body))
          (values branch-t (case-branch (case-branch-pat b) branch-e))))
      ;; find the lub of all the branch types
      (values (foldl1 type-lub branch-ts) (e-case subj-e branch-es))]

    [(or (e-fun _ _) (e-mono _ _) (e-fix _ _) (e-empty) (e-join _ _)
       (e-letin _ _ _))
      (type-error "can't infer type of: ~v" e)]))

;; returns elaborated expression.
(define (elab-check Γ t e)
  (match e
    ;; things that must be inferrable
    [(or (e-ann _ _) (e-var _ _) (e-lit _) (e-app _ _) (e-proj _ _))
      (define-values (et ee) (elab-infer Γ e))
      (unless (subtype? et t)
        (type-error "expression e has type: ~v\nbut we expect type: ~v" et t))
      ee]

    [(e-prim p)
      (if (prim-has-type? p t) e
        (type-error "primitive ~a cannot have type ~v" p t))]

    [(e-fun var body)
      (match t
        [(t-fun a b) (e-fun var (elab-check (env-cons (h-any a) Γ) b body))]
        [_ (type-error "not a function type: ~v" t)])]
    [(e-mono var body)
      (match t
        [(or (t-fun a b) (t-mono a b))
          (e-mono var (elab-check (env-cons (h-mono a) Γ) b body))]
        [_ (type-error "not a monotone function type: ~v" t)])]

    [(e-tuple es)
      (match t
        [(t-tuple ts)
          (e-tuple (map (curry elab-check Γ) es ts))]
        [_ (type-error "not a tuple type: ~v" t)])]

    [(e-tag name subj)
      (match t
        [(t-sum branches)
          (define (fail)
            (type-error "sum type ~v does not have branch ~a"
              branches name))
          (e-tag name (elab-check Γ (hash-ref branches name fail) subj))]
        [_ (type-error "not a sum type: ~v" t)])]

    [(e-case subj branches)
      ;; TODO: case completeness checking
      (define-values (subj-t subj-e) (elab-infer (env-hide-mono Γ) subj))
      (define sum-types
        (match subj-t
          [(t-sum h) h]
          [_ (type-error "can't case on expr of type ~v" subj-t)]))
      (e-case subj-e
        (for/list ([b branches])
          (match-define (case-branch p body) b)
          (define pat-env (check-pat Γ subj-t p))
          ;; is append right? use env-extend instead?
          (case-branch p
            ;; it's okay to use h-any here ONLY because we hid the monotone
            ;; environment when checking subj.
            (elab-check (append (map h-any pat-env) Γ) t body))))]

    [(e-empty)
      (unless (lattice-type? t) (error "not a lattice type: ~v" t))
      e]
    [(e-join l r)
      (unless (lattice-type? t) (error "not a lattice type: ~v" t))
      (e-join (elab-check Γ t l) (elab-check Γ t r))]

    [(e-singleton elem)
      (match t
        [(t-fs a) (e-singleton (elab-check (env-hide-mono Γ) a elem))]
        [_ (type-error "not a set type: ~v" t)])]

    [(e-letin var arg body)
      (define-values (arg-t arg-e) (elab-infer Γ arg))
      (define elem-t (match arg-t
                       [(t-fs a) a]
                       [_ (type-error "(letin) not a set type: ~v" arg-t)]))
      (e-letin var arg-e
        (elab-check (env-cons (h-any elem-t) Γ) body))]

    [(e-fix var body)
      (unless (fixpoint-type? t)
        (type-error "cannot take fixpoint at type: ~v" t))
      (e-fix var
        (elab-check (env-cons (h-mono t) Γ) body))]))

;; checks a pattern against a type and returns the env that the pattern binds.
(define (check-pat Γ t p)
  (match p
    [(p-wild) '()]
    [(p-var _) (list t)]
    [(p-lit l)
      (if (subtype? t (or (lit-type l) (type-error "unknown literal type")))
        '()
        (type-error "wrong type when matched against literal"))]
    [(p-tuple pats)
      (match t
        [(t-tuple types)
          (if (= (length types) (length pats))
            ;; why (append* (reverse ...))?
            (append* (reverse (map (curry check-pat Γ) types pats)))
            (type-error "wrong length tuple pattern"))]
        [_ (type-error "not a tuple")])]
    [(p-tag tag pat)
      (match t
        [(t-sum bs) (if (dict-has-key? bs tag)
                      (check-pat Γ (hash-ref bs tag) pat)
                      ;; FIXME: this is actually ok, it's just dead code; should
                      ;; warn, not error
                      (type-error "no such branch in tagged sum"))]
        [_ (type-error "not a sum")])]))
