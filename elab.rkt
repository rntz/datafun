#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

(define (type-error fmt . args)
  (error (apply format (string-append "type error: " fmt) args)))

;;; FIXME: the typechecker doesn't actually check the condition that, if there
;;; are monotone variables in the context, the expression we're checking must
;;; have a lattice type!
;;;
;;; I think this is OK, but it's *not* the type system outlined in the paper!


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

;; maps some exprs to info about them that is used for compilation:
;; - e-lam, e-app: 'fun or 'mono, for ordinary or monotone {lambdas,application}
;; - e-join, e-prim, e-fix: its type
(define *elab-info*  (make-weak-hasheq))
(define (elab-info e [orelse (lambda () (error "no elab info for:" e))])
  (hash-ref *elab-info* e orelse))

;; returns type & updates expr-elab-info.
(define (elab-infer e Γ)
  ;; (printf "(elab-infer ~v ~v)\n" Γ e)
  (define (set-info i) (hash-set! *elab-info* e i))
  (define (remember-type t) (set-info t) t)
  (match e
    [(e-ann t e) (elab-check e t Γ) t]
    [(e-lit v) (lit-type v)]

    [(e-var n i)
      (match (env-ref Γ i)
        [(or (h-any t) (h-mono t)) t]
        [_ (type-error "hidden monotone variable: ~a" n)])]

    [(e-prim p)
     (define t (prim-type-infer p))
     (unless t (type-error "can't infer type of primitive: ~a" p))
     (remember-type t)]

    [(e-app f a)
     (define ft (elab-infer f Γ))
     (match ft
       [(~> i o) (set-info 'mono) (elab-check a i Γ) o]
       [(-> i o) (set-info 'fun) (elab-check a i (env-hide-mono Γ)) o]
       [_ (type-error "applying non-function ~v, of type ~v" f ft)])]

    [(e-proj i subj)
     (define subj-t (elab-infer subj Γ))
     (match* (i subj-t)
       [((? number?) (t-tuple a))  #:when (< i (length a))    (list-ref a i)]
       [((? symbol?) (t-record a)) #:when (hash-has-key? a i) (hash-ref a i)]
       [(_ _) (type-error "invalid projection: ~v" e)])]

    [(e-record-merge l r)
     (t-record (hash-union-right (elab-infer-record l Γ)
                                 (elab-infer-record r Γ)))]

    ;; TODO: synthesize let-in  join expressions when possible, even though
    ;; it's non-standard?
    ;;
    ;; PROBLEM: synthesizing joins is tricksy! for exmaple, ({a:2, b:"foo"} join
    ;; {a:10}) has meaning, namely {a:10}. but then ({a:2, b:"foo"} join
    ;; {a:10,b:"fux"}) must have a meaning as well, or we violate liskov's
    ;; substitution principle! so now we need a function
    ;; least-lattice-supertype, that given a type A finds the least lattice type
    ;; M such that A <: M. this seems excessively magical.
    ;;
    ;; are there similar problems with let-in? indeed!
    ;;
    ;; NB. technically I shouldn't be synthesizing tuples, tagged values, or
    ;; singleton sets, since they're introduction forms. but w/e.
    [(e-tuple as) (t-tuple (for/list ([a as]) (elab-infer a Γ)))]

    [(e-record fields)
     (t-record (hash-map-values (lambda (x) (elab-infer x Γ)) fields))]

    [(e-tag name subj) (t-sum (hash name (elab-infer subj Γ)))]

    [(e-set '()) (type-error "can't infer type of empty set")]
    [(e-set elems)
     (define new-Γ (env-hide-mono Γ))
     (FS (foldl1 type-lub (for/list ([a elems]) (elab-infer a new-Γ))))]

    [(e-case subj branches)
     (when (null? branches)
       (type-error "can't infer type of case with no branches"))
     (define subj-t (elab-infer subj (env-hide-mono Γ)))
     ;; find the lub of all the branch types
     (define (branch-type b)
       (match-define (case-branch pat body) b)
       ;; it's okay to use h-any here ONLY because we hid the monotone
       ;; environment when checking subj.
       (define pat-Γ (map h-any (check-pat Γ subj-t pat)))
       (elab-infer body (append pat-Γ Γ)))
     (foldl1 type-lub (map branch-type branches))]

    [(e-let kind v subj body)
     (define hyp    (match kind ['mono h-mono] ['any h-any]))
     (define subj-Γ (match kind ['mono Γ]      ['any (env-hide-mono Γ)]))
     (define subj-t (elab-infer subj subj-Γ))
     (elab-infer body (env-cons (hyp subj-t) Γ))]

    [(or (e-lam _ _) (e-fix _ _) (e-join _) (e-letin _ _ _))
      (type-error "can't infer type of: ~v" e)]))

;; returns nothing.
(define (elab-check e t Γ)
  (define (set-info i) (hash-set! *elab-info* e i))
  (define (remember-type) (set-info t))
  ;; (printf "(elab-check ~v ~v ~v)\n" Γ t e)
  (match e
    ;; things that must be inferrable
    ;; TODO: maybe allow checking e-record-merge?
    [(or (e-ann _ _) (e-var _ _) (e-lit _) (e-app _ _) (e-proj _ _)
         (e-record-merge _ _))
     (define et (elab-infer e Γ))
     (unless (subtype? et t)
       (type-error "expression e has type: ~v\nbut we expect type: ~v" et t))]

    [(e-prim p) (if (prim-has-type? p t) (remember-type)
                    (type-error "primitive ~a cannot have type ~v" p t))]

    [(e-lam var body)
     (define-values (k h b)
       (match t
         [(t-mono a b) (values 'mono (h-mono a) b)]
         [(t-fun a b) (values 'fun (h-any a) b)]
         [_ (type-error "not a function type: ~v" t)]))
     (set-info k)
     (elab-check body b (env-cons h Γ))]

    [(e-tuple es)
      (match t
        [(t-tuple ts)
         (if (= (length es) (length ts))
          (for ([e es] [t ts]) (elab-check e t Γ))
          (type-error "wrong-length tuple: ~v" e))]
        [_ (type-error "not a tuple type: ~v" t)])]

    [(e-record fields)
     (define field-types
       (match t [(t-record fs) fs]
                [_ (type-error "not a record type: ~v" t)]))
     (for ([(n e) fields])
       ;; TODO: technically this should be a warning.
       (define (err) (type-error "(WARNING) unnecessary field: ~a" n))
       (elab-check e (hash-ref field-types n err) Γ))]

    [(e-tag name subj)
      (match t
        [(t-sum branches)
          (define (fail)
            (type-error "sum type ~v does not have branch ~a"
              branches name))
         (elab-check subj (hash-ref branches name fail) Γ)]
        [_ (type-error "not a sum type: ~v" t)])]

    [(e-case subj branches)
      ;; TODO: case completeness checking.
      ;;
      ;; TODO: think about when it might be ok not to hide the monotone
      ;; environment when typechecking the case-subject. I think only for
      ;; irrefutable patterns, a la (let p = e in e)?
     (define subj-t (elab-infer subj (env-hide-mono Γ)))
     (for ([b branches])
       (match-define (case-branch p body) b)
       (define pat-env (check-pat Γ subj-t p))
       ;; it's okay to use h-any here ONLY because we hid the monotone
       ;; environment when checking subj.
       (elab-check body t (append (map h-any pat-env) Γ)))]

    [(e-join as)
     (unless (lattice-type? t) (error "not a lattice type: ~v" t))
     (for ([a as]) (elab-check a t Γ))
     (remember-type)]

    [(e-set elems)
     (define new-Γ (env-hide-mono Γ))
     (match t
       [(t-fs a) (for ([elem elems]) (elab-check elem a new-Γ))]
       [_ (type-error "not a set type: ~v" t)])]

    [(e-letin var arg body)
     (define arg-t (elab-infer arg Γ))
     (define elem-t (match arg-t
                      [(t-fs a) a]
                      [_ (type-error "(letin) not a set type: ~v" arg-t)]))
     (elab-check body t (env-cons (h-any elem-t) Γ))
     (remember-type)]

    [(e-let kind v subj body)
     (define hyp    (match kind ['any h-any] ['mono h-mono]))
     (define subj-Γ (match kind ['any (env-hide-mono Γ)] ['mono Γ]))
     (define subj-t (elab-infer subj subj-Γ))
     (elab-check body t (env-cons (hyp subj-t) Γ))]

    [(e-fix var body)
     (unless (fixpoint-type? t)
       (type-error "cannot take fixpoint at type: ~v" t))
     (elab-check body t (env-cons (h-mono t) Γ))
     (remember-type)]))

(define (elab-infer-record e Γ)
  (match (elab-infer e Γ)
    [(t-record h) h]
    [_ (type-error "not a record: ~v" e)]))

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
                      (type-error "(WARNING) no such branch in tagged sum"))]
        [_ (type-error "not a sum")])]))
