#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "types.rkt" "env.rkt")
(provide (all-defined-out))

(define (prim-type-infer p)
  (match p
    ;; TODO?: extend <= to all equality types?
    ['<= (-> Nat (~> Nat Bool))]
    [(or '+ '*) (~> Nat Nat Nat)]
    ['- (~> Nat (-> Nat Nat))]
    ['++ (-> Str Str Str)]
    ['puts (~> Str (×))]
    [_ #:when (prim? p) #f]))

(define (prim-has-type? p t)
  (define pt (prim-type-infer p))
  (if pt (type=? t pt)
    (match* (p t)
      [('= (-> a b (t-bool)))
        (and (type=? a b) (eqtype? a))]
      [('subset? (-> (FS a) (~> (FS b) (t-bool))))
        (and (type=? a b) (eqtype? a))]
      [('print (~> _ (×))) #t]
      [(_ _) #f])))


;; Elaboration uses envs mapping bound variables to hyp(othese)s. h-any is an
;; unrestricted hyp; h-mono is a monotone hyp; h-hidden is a monotone hyp hidden
;; by entry into a constant expression (e.g. argument to a non-monotone
;; function).
;;
;; "Free" variables are always unrestricted, and are just mapped to their types.
(enum hyp (h-any type) (h-mono type) (h-hidden))

(define (env-hide-mono Γ)
  (env-map-bound (match-lambda [(h-mono _) (h-hidden)] [x x]) Γ))

(define (env-trustme Γ)
  (env-map-bound (match-lambda [(h-mono t) (h-any t)] [x x]) Γ))


;; The elaborator generates an info hashtable that maps some exprs to info about
;; them that is used for compilation:
;;
;; - e-lam, e-app: 'fun or 'mono, for ordinary or monotone {lambdas,application}
;; - e-join, e-join-in, e-prim, e-fix: its type
;;
;; TODO: currently the 'fun/'mono information is completely unused (see
;; compile.rkt)! should we remove it?

;; whether we need to remember the type of an expression
(define (should-remember-type expr)
  (match expr
    [(or (e-prim _) (e-join _) (e-join-in _ _ _) (e-fix _ _)) #t]
    [_ #f]))

;;; returns (values info-table type-of-expr)
;;; if `type' is #f, we infer the type of `expr'.
;;; otherwise, we check that `expr' has type `type'.
(define (elab root-expr #:type [root-type #f] #:env [root-Γ empty-env])
  (define info-table (make-hasheq))
  (define (set-info! e i)
    (assert! (not (hash-has-key? info-table e)))
    (hash-set! info-table e i))

  ;; if `type' is #f, we're inferring.
  ;; if not, we're checking.
  ;; returns the type of `expr', which is always be a subtype of `type'.
  (define (visit expr type Γ)
    (define expr-type (find-type expr type Γ))
    (when (should-remember-type expr)
      (set-info! expr expr-type))
    ;; TODO?: optimization: use eq? to avoid call to subtype? here
    (when (and type (not (subtype? expr-type type)))
      (type-error
"        expression: ~s
          has type: ~s
but we expect type: ~s"
                  (expr->sexp expr)
                  (type->sexp expr-type)
                  (type->sexp type)))
    expr-type)

  ;; if `type' is #f, we're inferring. if not, we're checking.
  (define (find-type expr type Γ)
    (define (fail [why #f] . format-args)
      (define message
       (if type
           (format "expression: ~s
cannot be given type: ~s" (expr->sexp expr) (type->sexp type))
           (format "cannot infer type of expression: ~s" (expr->sexp expr))))
      (when why
        (define why-msg (apply format (string-append why) format-args))
        (set! message (string-append message "\nreason: " why-msg)))
      (type-error message))

    ;; ---------- COMMENCE BIG GIANT CASE ANALYSIS ----------
    (match expr
      ;; ===== TRANSPARENT / BOTH SYNTHESIS AND ANALYSIS EXPRESSIONS =====
      [(e-trustme e) (visit e type (env-trustme Γ))]

      [(e-let tone v subj body)
       (define hyp    (match tone ['mono h-mono] ['any h-any]))
       (define subj-Γ (match tone ['mono Γ]      ['any (env-hide-mono Γ)]))
       (define subj-t (visit subj #f subj-Γ))
       (visit body type (env-cons (hyp subj-t) Γ))]

      ;; ===== SYNTHESIS-ONLY EXPRESSIONS =====
      ;; we infer these, and our caller checks the inferred type if necessary
      [(e-ann t e) (visit e t Γ) t]
      [(e-lit v) (lit-type v)]

      [(e-free-var n)
       (env-free-ref Γ n (lambda () (fail "it is a free variable")))]

      [(e-var n i)
       (define (unbound) (fail "it is an unbound variable (BAD PARSE)"))
       (match (env-ref Γ i unbound)
         [(or (h-any t) (h-mono t)) t]
         [_ (fail "it is a hidden monotone variable")])]

      [(e-app f a)
       (define ft (visit f #f Γ))
       (match ft
         [(~> i o) (set-info! expr 'mono) (visit a i Γ) o]
         [(-> i o) (set-info! expr 'fun) (visit a i (env-hide-mono Γ)) o]
         [_ (fail "applying non-function ~s : ~s"
                  (expr->sexp f) (type->sexp ft))])]

      [(e-proj i subj)
       (define subj-t (visit subj #f Γ))
       (match* (i subj-t)
         [((? number?) (t-tuple a))  #:when (< i (length a))    (list-ref a i)]
         [((? symbol?) (t-record a)) #:when (hash-has-key? a i) (hash-ref a i)]
         [(_ _) (fail "bad projection")])]

      [(e-record-merge l r)
       (define (infer-record e)
         (match (visit e #f Γ)
           [(t-record h) h]
           ;; TODO: better error message
           [t (fail "merge argument is not a record: ~s : ~s"
                    (expr->sexp e) (type->sexp t))]))
       (t-record (hash-union-right (infer-record l) (infer-record r)))]

      ;; ===== ANALYSIS-ONLY TERMS ====
      ;; we need `type' to be non-#f to check these
      [(e-lam _ _) #:when (not type) (fail "lambdas not inferrable")]
      [(e-lam var body) #:when type
       (define-values (tone hyp body-type)
         (match type
           [(t-mono a b) (values 'mono (h-mono a) b)]
           [(t-fun a b)  (values 'fun  (h-any a)  b)]
           [_ (fail "lambdas must have function type")]))
       (set-info! expr tone)
       (visit body body-type (env-cons hyp Γ))
       type]

      [(e-fix _ _) #:when (not type) (fail "fix expressions not inferrable")]
      [(e-fix var body) #:when type
       (unless (fixpoint-type? type)
         (fail "cannot calculate fixpoints of type ~s" (type->sexp type)))
       (visit body type (env-cons (h-mono type) Γ))]

      [(e-join as) #:when (not type) (fail "join expressions not inferrable")]
      [(e-join as) #:when type
       (unless (lattice-type? type)
         (error "cannot join at non-lattice type ~s" (type->sexp type)))
       (for ([a as]) (visit a type Γ))
       type]

      [(e-join-in _ _ _) #:when (not type)
       (fail "join expressions not inferrable")]
      [(e-join-in var arg body) #:when type
       (define elem-type
         (match (visit arg #f Γ)
           [(t-fs a) a]
           ;; TODO: better error message
           [t (fail "iteratee has non-set type ~s" (type->sexp t))]))
       (visit body type (env-cons (h-any elem-type) Γ))]

      ;; ===== ANALYSIS (BUT SOMETIMES SYNTHESIZABLE) EXPRESSIONS =====
      ;;
      ;; we can synthesize these (assuming their subterms synthesize), so we do,
      ;; even though it's non-standard.
      ;;
      ;; TODO: synthesize join and join-in expressions when possible
      [(e-prim p) #:when type (if (prim-has-type? p type) type (fail))]
      [(e-prim p) (let ([t (prim-type-infer p)])
                    (if t t (fail)))]

      [(e-tuple as)
       (match type
         [#f (t-tuple (for/list ([a as]) (visit a #f Γ)))]
         [(t-tuple ts) (if (= (length as) (length ts))
                           (begin0 type (for ([a as] [t ts]) (visit a t Γ)))
                           (fail "tuple length mismatch"))]
         [_ (fail "tuple expression must have tuple type")])]

      [(e-record fields)
       (match type
         [#f (t-record (hash-map-values (lambda (x) (visit x #f Γ)) fields))]
         [(t-record field-types)
          ;; we return the inferred type, and the subtype check will ensure it
          ;; has all the necessary fields.
          (t-record (for/hash ([(n e) fields])
                      (define (err) (fail "extra field: ~a" n))
                      (values n (visit e (hash-ref field-types e err)))))]
         [_ (fail "record expression must have record type")])]

      [(e-tag name subj)
       (match type
         [#f (t-sum (hash name (visit subj #f Γ)))]
         [(t-sum branches)
          (define (err) (fail "no such branch in sum type: ~a" name))
          (visit subj (hash-ref branches name err) Γ)
          type]
         [_ (fail "tagged expression must have sum type")])]

      [(e-set '()) (or type (fail "can't infer type of empty set"))]
      [(e-set elems)
       (define new-Γ (env-hide-mono Γ))
       (match type
         [#f (FS (foldl1 type-lub (for/list ([a elems]) (visit a #f new-Γ))))]
         [(t-fs a) (for ([elem elems]) (visit elem a new-Γ)) type]
         [_ (fail "set expression must have set type")])]

      [(e-case _ '()) #:when (not type)
       (fail "can't infer type of case with no branches")]
      [(e-case subj branches)
       ;; TODO: case completeness checking.
       ;;
       ;; TODO: think about when it might be ok not to hide the monotone
       ;; environment when typechecking the case-subject. I think only for
       ;; irrefutable patterns, a la (let p = e in e)?
       (define subj-t (visit subj #f (env-hide-mono Γ)))
       ;; find the lub of all the branch types
       (define (check-branch b)
         (match-define (case-branch pat body) b)
         ;; it's okay to use h-any here ONLY because we hid the monotone
         ;; environment when checking subj.
         (define pat-hyps (map h-any (check-pat Γ subj-t pat)))
         (visit body type (env-extend Γ pat-hyps)))
       (if type
           (begin0 type (for ([b branches]) (check-branch b)))
           (foldl1 type-lub (map check-branch branches)))])
    ;; ---------- END BIG GIANT CASE ANALYSIS ----------
    )

  ;; we annotate errors with the whole expression for context
  (define (on-err e)
    (error (format "~a
when typechecking expression: ~s" (exn-message e) (expr->sexp root-expr))))

  (with-handlers ([exn:type-error? on-err])
   (values info-table (visit root-expr root-type root-Γ))))

;; checks a pattern against a type and returns the env that the pattern binds.
;; returns list of types of variables the pattern binds.
;; e.g. (p-tuple (p-var X) (p-var Y)) --> (list X's-type Y's-type)
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
            (append* (map (curry check-pat Γ) types pats))
            (type-error "wrong length tuple pattern"))]
       [_ (type-error "not a tuple")])]
    [(p-tag tag pat)
     (match t
       [(t-sum bs) (if (dict-has-key? bs tag)
                       (check-pat Γ (hash-ref bs tag) pat)
                       ;; TODO: this is actually ok, it's just dead code; should
                       ;; warn, not error
                       (type-error "(WARNING) no such branch in tagged sum"))]
       [_ (type-error "not a sum")])]))
