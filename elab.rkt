#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

(define (type-error fmt . args)
  (error (apply format (string-append "type error: " fmt) args)))


;; Type utilities.
(define/match (subtype? a b)
  [((t-tuple as) (t-tuple bs)) (eqmap subtype? as bs)]
  [((t-record as) (t-record bs))
    (for/and ([(k v) bs])
      (and (hash-has-key? as k) (subtype? (hash-ref as k) v)))]
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
  [((t-record as) (t-record bs)) (t-record (hash-union-with as bs type-glb))]
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

;; Elaborated expression forms to distinguish ordinary from monotone functions
;; and applications.
(struct e-lam-fun e-lam () #:transparent)
(struct e-lam-mono e-lam () #:transparent)

(struct e-app-fun e-app () #:transparent)
(struct e-app-mono e-app () #:transparent)


;;; Inference & checking.
;; returns two values: type & elaborated expression.
(define (elab-infer Γ e)
  ;; (printf "(elab-infer ~v ~v)\n" Γ e)
  (define (ok t) (values t e))
  (match e
    [(e-ann t e) (values t (e-ann t (elab-check Γ t e)))]
    [(e-lit v) (ok (lit-type v))]

    [(e-var n i)
      (match (env-ref Γ i)
        [(or (h-any t) (h-mono t)) (ok t)]
        [_ (type-error "hidden monotone variable: ~a" n)])]

    [(e-prim p)
      (define t (prim-type-infer p))
      (if t (ok t)
        (type-error "can't infer type of primitive: ~a" p))]

    [(e-app f a)
      (define-values (ft fe) (elab-infer Γ f))
      ;; (printf "function ~v has type ~v\n" f ft)
      (match ft
        [(~> i o) (values o (e-app-mono fe (elab-check Γ i a)))]
        [(-> i o) (values o (e-app-fun fe (elab-check (env-hide-mono Γ) i a)))]
        [_ (type-error "applying non-function ~v, of type ~v" f ft)])]

    [(e-proj i subj)
     (define-values (subj-t subj-e) (elab-infer Γ subj))
     (values
      (match* (i subj-t)
        [((? number?) (t-tuples a)) #:when (< i (length a)) (list-ref a i)]
        [((? symbol?) (t-record a)) #:when (hash-has-key? a i) (hash-ref a i)]
        [(_ _) (type-error "invalid projection: ~v" subj-e)])
      (e-proj i subj-e))]

    ;; TODO: synthesize let-in and join expressions when possible, even though
    ;; it's non-standard.
    ;;
    ;; NB. technically I shouldn't be synthesizing tuples, tagged values, or
    ;; singleton sets, since they're introduction forms. but w/e.
    [(e-tuple as)
      (define-values (ts es)
        (for/lists (ts es) ([a as]) (elab-infer Γ a)))
      (values (t-tuple ts) (e-tuple es))]

    [(e-record fields)
     (define (f e) (call-with-values (lambda () (elab-infer Γ e)) cons))
     (define h (hash-map-values f fields))
     (values (t-record (hash-map-values car h))
             (e-record base-expr (hash-map-values cdr h)))]

    [(e-record-merge l r)
     (define-values (l-fields l-expr) (elab-infer-record Γ l))
     (define-values (r-fields r-expr) (elab-infer-record Γ r))
     (values (t-record (hash-union-right l-fields r-fields))
             (e-record-merge l-expr r-expr))]

    [(e-tag name subj)
      (define-values (subj-t subj-e) (elab-infer Γ subj))
      (values (Σ (name subj-t)) (e-tag name subj-e))]

    [(e-singleton subj)
      (define-values (subj-t subj-e) (elab-infer (env-hide-mono Γ) subj))
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

    [(e-let kind v subj body)
     (define hyp    (match kind ['mono h-mono] ['any h-any]))
     (define subj-Γ (match kind ['mono Γ]      ['any (env-hide-mono Γ)]))
     (define-values (subj-t subj-e) (elab-infer subj-Γ subj))
     (define-values (body-t body-e) (elab-infer (env-cons (hyp subj-t) Γ) body))
     (values body-t (e-let kind v subj-e body-e))]

    [(or (e-lam _ _) (e-fix _ _) (e-empty) (e-join _ _) (e-letin _ _ _))
      (type-error "can't infer type of: ~v" e)]))

;; returns elaborated expression.
(define (elab-check Γ t e)
  ;; (printf "(elab-check ~v ~v ~v)\n" Γ t e)
  (match e
    ;; things that must be inferrable
    ;; TODO: maybe allow checking e-record-merge?
    [(or (e-ann _ _) (e-var _ _) (e-lit _) (e-app _ _) (e-proj _ _)
         (e-record-merge _ _))
      (define-values (et ee) (elab-infer Γ e))
      (unless (subtype? et t)
        (type-error "expression e has type: ~v\nbut we expect type: ~v" et t))
      ee]

    [(e-prim p)
      (if (prim-has-type? p t) e
        (type-error "primitive ~a cannot have type ~v" p t))]

    [(e-lam var body)
      (match t
        [(t-mono a b)
          (e-lam-mono var (elab-check (env-cons (h-mono a) Γ) b body))]
        [(t-fun a b)
          (e-lam-fun var (elab-check (env-cons (h-any a) Γ) b body))]
        [_ (type-error "not a function type: ~v" t)])]

    [(e-tuple es)
      (match t
        [(t-tuple ts)
          (e-tuple (map (curry elab-check Γ) es ts))]
        [_ (type-error "not a tuple type: ~v" t)])]

    [(e-record fields)
     (define field-types
       (match t [(t-record fs) fs]
                [_ (type-error "not a record type: ~v" t)]))
     (e-record
      (for/hash ([(n e) fields])
        ;; TODO: technically we should allow fields that aren't in the type
        ;; we're checking against. this seems unlikely to come up in practice.
        (define (err) (type-error "field of unspecified type: ~a" n))
        (values n (elab-check Γ (hash-ref field-types n err) e))))]

    [(e-tag name subj)
      (match t
        [(t-sum branches)
          (define (fail)
            (type-error "sum type ~v does not have branch ~a"
              branches name))
          (e-tag name (elab-check Γ (hash-ref branches name fail) subj))]
        [_ (type-error "not a sum type: ~v" t)])]

    [(e-case subj branches)
      ;; TODO: case completeness checking.
      ;;
      ;; TODO: think about when it might be ok not to hide the monotone
      ;; environment when typechecking the case-subject.
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

    [(e-let kind v subj body)
     (define subj-Γ (match kind ['any (env-hide-mono Γ)] ['mono Γ]))
     (define hyp    (match kind ['any h-any] ['mono h-mono]))
     (define-values (subj-t subj-e) (elab-infer subj-Γ subj))
     (e-let kind v subj-e (elab-check (env-cons (hyp subj-t) Γ) t body))]

    [(e-fix var body)
      (unless (fixpoint-type? t)
        (type-error "cannot take fixpoint at type: ~v" t))
      (e-fix var
        (elab-check (env-cons (h-mono t) Γ) body))]))

;; returns (values fields expr-or-#f)
(define (elab-infer-record Γ e)
  (define-values (tt ee) (elab-infer Γ base))
  (values (match tt [(t-record h) h] [_ (type-error "not a record: ~v" ee)])
          ee))

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
