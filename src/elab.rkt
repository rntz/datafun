#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "types.rkt" "env.rkt")
(provide elab (struct-out hyp))

;; TODO: report source-info on type error
;; probably want to keep a stack of source-info spans or something.
;;
;; (require "source-info.rkt")

;; ========== Entry point ==========
;; returns (values info-table type-of-expr)
;; if `type' is #f, we infer the type of `expr'.
;; otherwise, we check that `expr' has type `type'.
;;
;; `env' is an env (see env.rkt) mapping variables to their (closed, i.e.
;; without use of t-name) types.
(define (elab root-expr #:type [root-type #f] #:env [root-env empty-env])
  (parameterize ([elab-info (make-hasheq)]
                 [elab-env root-env])
    (define type
      (if root-type
          (expr-check-annotated root-expr root-type)
          (expr-check root-expr)))
    ;; must call (elab-info) *after* running expr-check, since expr-check
    ;; updates elab-info.
    (values (elab-info) type)))


;;; ===== Error messages =====
(define expr-stack (make-parameter '()))

(define (top-expr) (last (expr-stack)))
(define (current-expr) (first (expr-stack)))

;; TODO?: rename elab-error to expr-error?
;; we annotate errors with the whole expression for context
(define (elab-error fmt . args) (elab-error-raw (apply format fmt args)))
(define (elab-error-raw msg)
  (type-error "when typechecking expression: ~s
sub-expression: ~s
~a" (expr->sexp (top-expr)) (expr->sexp (current-expr)) msg))


;; ========== Primitives and their types ==========
(define (prim-type-infer p)
  ((lambda (x) (and x (parse-type x)))
   (match p
     [(or '+ '*) '(nat nat ~> nat)]
     ['- '(nat ~> nat ->- nat)]
     ['++ '(str str -> str)]
     ['puts '(str -> (*))]
     ['strlen '(str -> nat)]
     ['substr '(str nat nat -> str)]
     [_ #:when (prim? p) #f])))

(define (prim-has-type? p t)
  (define pt (prim-type-infer p))
  (if pt
      (subtype? pt t)
      (match* (p t)
        [('= (t-fun 'any a (t-fun 'any b (t-base 'bool)))) (eqtype=? a b)]
        [('<= (t-fun (or 'anti 'any) a
                     (t-fun (or 'mono 'any) b (t-base 'bool))))
         (eqtype=? a b)]
        [('size (t-fun (or 'mono 'any) (t-set a) (t-base 'nat))) (eqtype? a)]
        [('keys (t-fun (or 'mono 'any) (t-map a _) (t-set b))) (eqtype=? a b)]
        [('lookup (t-fun (or 'mono 'any)
                         (t-map k v1)
                         (t-fun 'any k (t-sum (hash-table ['none (list)]
                                                          ['just (list v2)]
                                                          [_ _] ...)))))
         ;; as long as v1 & v2 are type-compatible we're ok.
         (type-compatible? v1 v2)]
        ;; print is actually *bitonic*, since it's constant, but we don't have a
        ;; way to represent that in its type.
        [('print (t-fun _ _ (t-tuple '()))) #t]
        [(_ _) #f])))


;; ========== Elab info ==========

;; The elaborator generates an info hashtable that maps some exprs to their
;; types. This is later used during compilation (see compile.rkt).
;;
;; elab-info is the parameter holding that hashtable. It is written to during
;; elaboration.
(define elab-info (make-parameter #f))
(define (set-info! e i)
  (assert! (not (hash-has-key? (elab-info) e)))
  (hash-set! (elab-info) e i))

;; whether we need to remember the type of an expression
(define/match (should-remember-type? expr)
  [((or (e-lub _) (e-set-bind _ _ _) (e-map-bind _ _ _ _) (e-map-get _ _)
        (e-cond _ _ _) (e-fix _ _))) #t]
  ;; we actually don't need to remember primitives; see do-prim in compile.rkt
  ;; [((e-prim _)) #t]
  [(_) #f])


;; ========== Elaboration envs ==========
;;
;; Elaboration uses envs (see env.rkt) mapping bound variables to hyp(othese)s.
;; Hypotheses are annotated with their tones & their types. tones can be:
;;
;; - 'any, for ordinary unrestricted variables
;; - 'mono, for monotone variables
;; - 'anti, for antitone variables
;; - #f, for previously-monotone variables hidden by entry into a constant
;;   expression
(struct hyp (tone type) #:transparent)

;; elab-env is the parameter holding the current env.
(define/contract elab-env (parameter/c env?) (make-parameter #f))

(define-syntax-rule (with-var var info body ...)
  (parameterize ([elab-env (env-bind-var var info (elab-env))]) body ...))
(define-syntax-rule (with-env var-hash body ...)
  (parameterize ([elab-env (env-bind-vars var-hash (elab-env))]) body ...))
(define-syntax-rule (with-tone tone body ...)
  (parameterize ([elab-env (env-for-tone tone (elab-env))]) body ...))
(define-syntax-rule (with-type-definition name type body ...)
  (parameterize ([elab-env (env-bind-type name type (elab-env))]) body ...))

(define (env-for-tone tone Γ)
  (match tone
    ['mono Γ]
    ;; reverse the polarity!
    ['anti (env-map-vars (match-lambda [(hyp o t) (hyp (tone-inverse o) t)]) Γ)]
    ['any (env-map-vars (match-lambda [(hyp (not 'any) t) (hyp #f t)] [x x]) Γ)]
    ;; hilarious hack
    ['trustme
     (env-map-vars (match-lambda [(hyp (not #f) t) (hyp 'any t)] [x x]) Γ)]))


;;; ========== Expression elaboration ==========

;; checks an expression annotated with a type. is unlike expr-check in that it
;; checks whether `type' is closed, and raises a type errors with a useful
;; message if it isn't.
(define/contract (expr-check-annotated expr type)
  (-> expr? type? type-wf?)
  (define (no-such-type n)
    (elab-error "cannot understand type: ~s
type name is not defined: ~a" (type->sexp type) n))
  (expr-check expr
   (parameterize ([expr-stack (cons expr (expr-stack))])
     (env-subst-type (elab-env) type no-such-type))))

;; if `type' is #f, we're inferring.
;; if not, we're checking.
;; returns the type of `expr', which is always be a subtype of `type'.
;; TODO: rename to elab-expr?
(define/contract (expr-check expr [type #f])
  (->* (expr?) ((or/c type-wf? #f)) type-wf?)
  (parameterize ([expr-stack (cons expr (expr-stack))])
    (define expr-type (infer expr type))

    ;; remember if necessary
    (when (should-remember-type? expr)
      (set-info! expr expr-type))

    ;; check (expr-type <: type).
    (when (and type (not (subtype? expr-type type)))
      (elab-error
"has type:      ~s
but we expect: ~s" (type->sexp expr-type) (type->sexp type)))

    ;; well-formedness checks on expr-type.
    (match expr-type
      [(t-map k v) #:when (not (eqtype? k))
       (elab-error "has map type: ~s
but key type ~s is not an equality type" (type->sexp expr-type) (type->sexp k))]
      [_ (void)])

    expr-type))

;; bad name.
;; if `type' is #f, we're inferring. if not, we're checking.
(define/contract (infer expr type)
  (expr? (or/c type-wf? #f) . -> . type-wf?)
  (define (fail-raw msg)
    (if type
        (elab-error "cannot be given type: ~s\n~a" (type->sexp type) msg)
        (elab-error "cannot infer type of sub-expression\n~a" msg)))
  (define (fail [fmt #f] . fmt-args)
    (fail-raw (if fmt (apply format fmt fmt-args) "")))

  (define (ensure-lattice-type
           t #:message [msg "cannot take lub at non-lattice type ~s"])
    (unless (lattice-type? t) (fail msg (type->sexp t)))
    t)

  ;; ---------- COMMENCE BIG GIANT CASE ANALYSIS ----------
  ;; TODO: turn this into a match* on (expr type)?
  (match expr
    ;; ===== SPECIAL CASES FOR INFERRING PRIMITIVES =====
    ;; it would be nice if somehow we didn't need this *and* prim-has-type?
    [(e-app (and prim-expr (e-prim (and p (or '= '<= 'size 'print)))) arg)
     (define tone (match p
                    ['= 'any]
                    ['<= 'anti]
                    [(or 'size 'print 'get) 'mono]))
     (define arg-type (with-tone tone (expr-check arg)))
     (define result-type (match p
                           ['print (t-tuple '())]
                           ['size (t-base 'nat)]
                           ['= (t-fun 'any arg-type (t-base 'bool))]
                           ['<= (t-fun 'mono arg-type (t-base 'bool))]))
     (expr-check prim-expr (t-fun tone arg-type result-type))
     result-type]

    [(e-app (e-prim 'keys) arg)
     (match (expr-check arg)
       [(t-map k v) (t-set k)]
       [t (fail "argument to `keys' of non-map type ~s" (type->sexp t))])]

    [(e-app (e-prim 'lookup) arg)
     (match (expr-check arg)
       [(t-map k v) (t-fun 'any k (t-sum (hash 'none '() 'just (list v))))]
       [t (fail "argument to `lookup' of non-map type ~s" (type->sexp t))])]

    ;; ===== TRANSPARENT / BOTH SYNTHESIS AND ANALYSIS EXPRESSIONS =====
    [(e-trustme e) (with-tone 'trustme (expr-check e type))]

    [(e-let tone var subj body)
     (define subj-t (with-tone tone (expr-check subj)))
     (with-var var (hyp tone subj-t) (expr-check body type))]

    [(e-let-type name type body)
     (with-type-definition name type (expr-check body type))]

    [(e-cond tone subj body)
     (unless (match? tone 'mono 'anti)
       ;; TODO: better error message.
       (type-error "bad tone for e-cond: ~a" tone))
     (with-tone tone (expr-check subj (t-base 'bool)))
     (ensure-lattice-type (expr-check body type))]

    [(e-set-bind pat arg body)
     (match (expr-check arg)
       [(t-set elem-type)
        (ensure-lattice-type
         (with-env (pat-hyps 'any pat elem-type)
           (expr-check body type)))]
       ;; TODO: better error message
       [t (fail "iteratee has non-set type ~s" (type->sexp t))])]

    [(e-map-bind key-pat value-var arg body)
     (match (expr-check arg)
       [(t-map key-type value-type)
        (ensure-lattice-type
         ;; We need not be monotone in the keys, since increasing keys does not
         ;; increase the map, only adding more keys does.
         (with-env (pat-hyps 'any key-pat key-type)
           ;; But we must be monotone in the value, since maps increase as their
           ;; values increase.
           (with-var value-var (hyp 'mono value-type)
             (expr-check body type))))]
       [t (fail "iteratee has non-map type ~s" (type->sexp t))])]

    ;; ===== SYNTHESIS-ONLY EXPRESSIONS =====
    ;; we infer these, and our caller checks the inferred type if necessary
    ;; TODO: better error message for unbound type names
    [(e-ann t e) (expr-check-annotated e t)]
    [(e-lit v) (lit-type v)]

    [(e-var n)
     (match (env-ref-var (elab-env) n (lambda () (fail "~a is not bound" n)))
       ;; TODO: better error message.
       [(hyp #f _) (fail "variable ~a is hidden due to tonicity" n)]
       ;; [(hyp (or 'any 'mono) t) t]
       ;; [(hyp 'anti t) (fail "~a is an antitone variable" n)]
       ;; alternative way to phrase this:
       [(hyp o t) #:when (subtone? o 'mono) t]
       [(hyp _ _) (fail "non-monotone use of variable ~a" n)])]

    [(e-app func arg)
     (match (expr-check func)
       [(t-fun o a b)
        (with-tone o (expr-check arg a))
        b]
       [func-type (fail "applying non-function ~s : ~s"
                        (expr->sexp func) (type->sexp func-type))])]

    [(e-proj i subj)
     (match* (i (expr-check subj))
       [((? number?) (t-tuple a))  #:when (< i (length a))    (list-ref a i)]
       [((? symbol?) (t-record a)) #:when (hash-has-key? a i) (hash-ref a i)]
       ;; TODO: better error message
       [(_ _) (fail "bad projection")])]

    [(e-record-merge l r)
     (define (infer-record e)
       (match (expr-check e)
         [(t-record h) h]
         ;; TODO: better error message
         [t (fail "merge argument is not a record: ~s : ~s"
                  (expr->sexp e) (type->sexp t))]))
     (t-record (hash-union-right (infer-record l) (infer-record r)))]

    [(e-map-get map-expr key-expr)
     (match (expr-check map-expr)
       [(t-map k v)
        (ensure-lattice-type v #:message "cannot `get' at non-lattice type ~s")
        (expr-check key-expr k)
        v]
       [t (fail "`get' from non-map of type ~s" (type->sexp t))])]

    [(e-map-for x keys body)
     (match (expr-check keys)
       [(t-set key-type)
        (t-map key-type
               (with-var x (hyp 'any key-type) (expr-check body)))]
       [t (fail "iterating over non-set type ~s" (type->sexp t))])]

    ;; ===== ANALYSIS-ONLY TERMS ====
    ;; we need `type' to be non-#f to check these
    [(e-lam _ _) #:when (not type) (fail "lambdas are not inferrable")]
    [(e-lam var body) #:when type
     (match-define (t-fun tone a body-type) type)
     (with-var var (hyp tone a)
       (expr-check body body-type))
     type]

    [(e-fix _ _) #:when (not type) (fail "fix expressions are not inferrable")]
    [(e-fix var body) #:when type
     (unless (fixpoint-type? type)
       (fail "cannot calculate fixpoints of type ~s" (type->sexp type)))
     (with-var var (hyp 'mono type)
       (expr-check body type))]

    ;; ===== ANALYSIS (BUT SOMETIMES SYNTHESIZABLE) EXPRESSIONS =====
    ;;
    ;; we can synthesize these (assuming their subterms synthesize), so we do,
    ;; even though it's non-standard.
    ;;
    ;; TODO: synthesize lub expressions when possible
    [(e-prim p) #:when type (if (prim-has-type? p type) type (fail))]
    [(e-prim p) (let ([t (prim-type-infer p)])
                  (if t t (fail)))]

    [(e-tuple as)
     (match type
       [#f (t-tuple (map expr-check as))]
       [(t-tuple ts) #:when (length=? as ts)
        (map expr-check as ts)
        type]
       [(t-tuple _) (fail "tuple length mismatch")]
       [_ (fail "tuple expression must have tuple type")])]

    [(e-record fields)
     (match type
       [#f (t-record (hash-map-vals expr-check fields))]
       [(t-record field-types)
        ;; we return the inferred type, and the subtype check will ensure it
        ;; has all the necessary fields.
        (t-record (for/hash ([(n e) fields])
                    (define (err) (fail "extra field: ~a" n))
                    (values n (expr-check e (hash-ref field-types e err)))))]
       [_ (fail "record expression must have record type")])]

    [(e-tag name exprs)
     (match type
       [#f (t-sum (hash name (map expr-check exprs)))]
       [(t-sum branches)
        (define (err) (fail "no such branch in sum type: ~a" name))
        (define types (hash-ref branches name err))
        (unless (length=? types exprs)
          ;; TODO: better error message
          (fail "constructor length mismatch"))
        (for ([e exprs] [t types]) (expr-check e t))
        type]
       [_ (fail "tagged expression must have sum type")])]

    [(e-lub '()) #:when (not type) (fail "can't infer type of empty lub")]
    [(e-lub as)
     (define types (for/list ([a as]) (expr-check a type)))
     (ensure-lattice-type (or type (foldl1 type-lub types)))]

    [(e-set '()) #:when (not type) (fail "can't infer type of empty set")]
    [(e-set elems)
     (with-tone 'any
       (match type
         [#f (t-set (foldl1 type-lub (map expr-check elems)))]
         [(t-set a) (for ([elem elems]) (expr-check elem a)) type]
         [_ (fail "set expression must have set type")]))]

    [(e-map '()) #:when (not type) (fail "can't infer type of empty map")]
    [(e-map `((,keys ,values) ...))
     ;; NB. we don't need to check the key type is an equality type; expr-check
     ;; will do that for us.
     (match type
       [#f (t-map (foldl1 type-lub (with-tone 'any (map expr-check keys)))
                  (foldl1 type-lub (map expr-check values)))]
       [(t-map kt vt)
        (with-tone 'any (for ([k keys]) (expr-check k kt)))
        (for ([v values]) (expr-check v vt))
        type]
       [_ (fail "map expression must have map type")])]

    [(e-case _ '()) #:when (not type)
     (fail "can't infer type of case with no branches")]
    [(e-case subj branches)
     ;; TODO: case completeness checking.
     ;;
     ;; TODO: think about when it might be ok not to hide the monotone
     ;; environment when typechecking the case-subject. I think only for
     ;; irrefutable patterns, a la (let p = e in e)?
     (define subj-t (with-tone 'any (expr-check subj #f)))

     (define/match (visit-branch branch)
       [((case-branch pat body))
        ;; it's okay to use 'any here ONLY because we hid the monotone
        ;; environment when checking subj.
        (with-env (pat-hyps 'any pat subj-t)
          (expr-check body type))])

     (define branch-types (map visit-branch branches))
     (or type (foldl1 type-lub branch-types))])
  ;; ---------- END BIG GIANT CASE ANALYSIS ----------
  )


;; ========== Pattern elaboration ==========

;; returns a hash mapping pattern variables to `hyp's containing their types and
;; the given tone.
(define (pat-hyps tone pat type)
  (hash-map-vals (curry hyp tone) (pat-check pat type)))

;; checks a pattern against a type and returns a hash mapping pattern
;; variables to their types.
;;
;; note that patterns are nonlinear - the same variable may be used multiple
;; times. if it is, this indicates an equality check. for example, (cons x x)
;; matches only pairs of two of the same value.
;;
;; TODO: better error messages - maybe keep a pat-stack, like expr-stack?
(define/match (pat-check p t)
  [((p-wild) _) (hash)]
  [((p-var name) t) (hash name t)]
  [((p-lit l) t)
   (if (subtype? t (or (lit-type l) (elab-error "unknown literal type")))
       (hash)
       (elab-error "wrong type when matched against literal"))]
  [((and pat (p-tuple pats)) (t-tuple types)) #:when (length=? pats types)
   (union-pat-envs (map pat-check pats types))]
  [((p-tuple _) (t-tuple _)) (elab-error "wrong length tuple pattern")]
  [((p-tuple _) t) (elab-error "not a tuple type: ~s" (type->sexp t))]
  [((p-tag tag pats) (t-sum bs))
   (define (err)
     ;; TODO: this is actually ok, it's just dead code; should warn, not error
     (elab-error "(WARNING) no such branch in tagged sum"))
   (define types (hash-ref bs tag err))
   (unless (length=? pats types)
     ;; TODO: better error message
     (elab-error "constructor length mismatch"))
   (union-pat-envs (map pat-check pats types))]
  [((p-tag _ _) _) (elab-error "not a sum")]
  [((and pat (p-and ps)) t)
   (union-pat-envs (map (lambda (p) (pat-check p t)) ps))]
  [((and pat (p-or ps)) t)
   (when (empty? ps)
     (elab-error "or-pattern cannot be empty: ~s" (pat->sexp pat)))
   (define hashes (for/list ([p ps]) (pat-check p t)))
   (define vars (hash-keyset (first hashes)))
   (unless (andmap (lambda (x) (equal? vars (hash-keyset x))) hashes)
     (elab-error "all branches of or-pattern must bind same variables: ~s"
                 (type->sexp pat)))
   (foldl1 (lambda (x y) (hash-union-with x y type-lub)) hashes)]
  [((p-let v body result-p) t)
   ;; FIXME: assumes we're matching with tonicity 'any
   (pat-check result-p (with-var v (hyp 'any t) (expr-check body)))])

(define (union-pat-envs hashes)
  (for/fold ([var-types (hash)]) ([h hashes])
    ;; we use type-glb because, when the same variable is used multiple times,
    ;; it must have a value which satisfies *all* of the types it is assigned.
    (hash-union-with var-types h eqtype-glb)))

;; finds glb of two types, checking that they are eqtypes. this is used for
;; combining types of pattern variables which are used multiple times. these
;; need to be eqtypes so that we can test equality; they are combined with
;; type-glb the variable must have a value which satisfies *all* the types it
;; was assigned.
;;
;; for this to be a reasonable approach requires that no equality type have a
;; non-equality supertype. luckily, this is true for Datafun.
(define (eqtype-glb a b)
  (define type (type-glb a b))
  (unless (eqtype? type)
    ;; TODO: better error message
    (elab-error "pattern variable used multiple times has non-equality type ~s"
                (type->sexp type)))
  type)
