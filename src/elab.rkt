#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "types.rkt" "env.rkt")
(provide elab (struct-out hyp))

;; The elaborator generates an info hashtable that maps some exprs to their
;; types. see should-remember-type?, below.

;;; returns (values info-table type-of-expr)
;;; if `type' is #f, we infer the type of `expr'.
;;; otherwise, we check that `expr' has type `type'.
(define (elab root-expr #:type [root-type #f] #:env [root-env empty-env])
  (parameterize ([elab-info (make-hasheq)]
                 [elab-env root-env])
    (define type (expr-check root-expr root-type))
    (values (elab-info) type)))

;; Elaboration uses envs mapping bound variables to hyp(othese)s. Hypotheses are
;; annotated with their tones & their types. tones can be:
;; - 'any, for ordinary unrestricted variables
;; - 'mono, for monotone variables
;; - 'anti, for antitone variables
;; - #f, for previously-monotone variables hidden by entry into a constant
;;   expression
(struct hyp (tone type) #:transparent)

(define (env-for-tone tone Γ)
  (match tone
    ['mono Γ]
    ;; reverse the polarity!
    ['anti (env-map (match-lambda [(hyp o t) (hyp (tone-inverse o) t)]) Γ)]
    ['any  (env-map (match-lambda [(hyp (not 'any) t) (hyp #f t)] [x x]) Γ)]
    ;; hilarious hack
    ['trustme
     (env-map (match-lambda [(hyp (not #f) t) (hyp 'any t)] [x x]) Γ)]))

(define/match (tone-inverse o)
  [('any) 'any]
  [('mono) 'anti]
  [('anti) 'mono]
  [(#f) #f])

(define-syntax-rule (with-tone tone body ...)
  (parameterize ([elab-env (env-for-tone tone (elab-env))]) body ...))


;;; Helper functions.
(define (prim-type-infer p)
  ((lambda (x) (and x (parse-type x)))
   (match p
     [(or '+ '*) '(nat nat ~> nat)]
     ['- '(nat ~> nat ->- nat)]
     ['++ '(str str -> str)]
     ['puts '(str -> (*))]
     [_ #:when (prim? p) #f])))

(define (prim-has-type? p t)
  (define pt (prim-type-infer p))
  (if pt
      (subtype? pt t)
      (match* (p t)
        [('= (t-fun 'any a (t-fun 'any b (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('<= (t-fun (or 'anti 'any) a
                     (t-fun (or 'mono 'any) b (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('size (t-fun (or 'mono 'any) (t-set a) (t-nat))) (eqtype? a)]
        ;; print is actually *bitonic*, since it's constant, but we don't have a
        ;; way to represent that in its type.
        [('print (t-fun _ _ (t-tuple '()))) #t]
        [(_ _) #f])))

;; whether we need to remember the type of an expression
(define/match (should-remember-type? expr)
  [((or (e-join _) (e-join-in _ _ _) (e-cond _ _ _) (e-fix _ _))) #t]
  ;; we actually don't need to remember primitives; see do-prim in compile.rkt
  ;; [((e-prim _)) #t]
  [(_) #f])


;;; ---------- PARAMETERS ----------
;;; these are used to communicate in the internals of elab
(define elab-info (make-parameter #f))
(define (set-info! e i)
  (assert! (not (hash-has-key? (elab-info) e)))
  (hash-set! (elab-info) e i))

(define elab-env (make-parameter #f))
(define-syntax-rule (with-var var id body ...)
  (parameterize ([elab-env (env-bind var id (elab-env))]) body ...))
(define-syntax-rule (with-env more-env body ...)
  (parameterize ([elab-env (env-extend (elab-env) more-env)]) body ...))

;;; ===== ERROR MESSAGE STUFF =====
(define expr-stack (make-parameter #f))

(define (top-expr) (last (expr-stack)))
(define (current-expr) (first (expr-stack)))

;; TODO?: rename elab-error to expr-error?
;; we annotate errors with the whole expression for context
(define (elab-error fmt . args) (elab-error-raw (apply format fmt args)))
(define (elab-error-raw msg)
  (type-error "when typechecking expression: ~s
sub-expression: ~s
~a" (expr->sexp (top-expr)) (expr->sexp (current-expr)) msg))


;;; ---------- INTERNALS ----------
;; if `type' is #f, we're inferring.
;; if not, we're checking.
;; returns the type of `expr', which is always be a subtype of `type'.
(define (expr-check expr [type #f])
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

    expr-type))

;; if `type' is #f, we're inferring. if not, we're checking.
(define (infer expr type)
  (define (fail-raw msg)
    (if type
        (elab-error "cannot be given type: ~s\n~a" msg)
        (elab-error "cannot infer type of sub-expression\n~a" msg)))
  (define (fail [fmt #f] . fmt-args)
    (fail-raw (if fmt (apply format fmt fmt-args) "")))

  (define (visit-branch tone pat-type body-type branch)
    (match-define (case-branch pat body) branch)
    (with-env (hash-map-values (curry hyp tone) (pat-check pat pat-type))
      (expr-check body body-type)))

  ;; ---------- COMMENCE BIG GIANT CASE ANALYSIS ----------
  ;; TODO: turn this into a match* on (expr type)?
  (match expr
    ;; ===== SPECIAL CASES FOR INFERRING PRIMITIVES =====
    ;; it would be nice if somehow we didn't need this *and* prim-has-type
    [(e-app (and prim-expr (e-prim (and p (or '= '<= 'size 'print)))) arg)
     (define tone (match p
                    ['= 'any]
                    ['<= 'anti]
                    [(or 'size 'print) 'mono]))
     (define arg-type (with-tone tone (expr-check arg)))
     (define result-type (match p
                           ['print (t-tuple '())]
                           ['size (t-nat)]
                           ['= (t-fun 'any arg-type (t-bool))]
                           ['<= (t-fun 'mono arg-type (t-bool))]))
     (expr-check prim-expr (t-fun tone arg-type result-type))
     result-type]

    ;; ===== TRANSPARENT / BOTH SYNTHESIS AND ANALYSIS EXPRESSIONS =====
    [(e-trustme e) (with-tone 'trustme (expr-check e type))]

    [(e-let tone var subj body)
     (define subj-t (with-tone tone (expr-check subj)))
     (with-var var (hyp tone subj-t) (expr-check body type))]

    [(e-cond tone subj body)
     (unless (matches? tone (or 'mono 'anti))
       ;; TODO: better error message.
       (type-error "bad tone for e-cond: ~a" tone))
     (with-tone tone (expr-check subj (t-bool)))
     (define body-type (expr-check body type))
     (unless (lattice-type? body-type)
       (fail "cannot join at non-lattice type ~s" (type->sexp body-type)))
     body-type]

    [(e-join-in pat arg body)
     (define elem-type
       (match (expr-check arg)
         [(t-set a) a]
         ;; TODO: better error message
         [t (fail "iteratee has non-set type ~s" (type->sexp t))]))
     (define body-type
       (visit-branch 'any elem-type type (case-branch pat body)))
     (unless (lattice-type? body-type)
       (error "cannot join at non-lattice type ~s" (type->sexp type)))
     body-type]

    ;; ===== SYNTHESIS-ONLY EXPRESSIONS =====
    ;; we infer these, and our caller checks the inferred type if necessary
    [(e-ann t e) (expr-check e t) t]
    [(e-lit v) (lit-type v)]

    [(e-var n)
     (match (env-ref (elab-env) n (lambda () (fail "~a is not bound" n)))
       ;; TODO: better error message.
       [(hyp #f _) (fail "variable ~a is hidden due to tonicity" n)]
       ;; [(hyp (or 'any 'mono) t) t]
       ;; [(hyp 'anti t) (fail "~a is an antitone variable" n)]
       ;; alternative way to phrase this:
       [(hyp o t) #:when (subtone? o 'mono) t]
       [(hyp _ _) (fail "non-monotone use of variable ~a" n)]
       )]

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
       [(_ _) (fail "bad projection")])]

    [(e-record-merge l r)
     (define (infer-record e)
       (match (expr-check e)
         [(t-record h) h]
         ;; TODO: better error message
         [t (fail "merge argument is not a record: ~s : ~s"
                  (expr->sexp e) (type->sexp t))]))
     (t-record (hash-union-right (infer-record l) (infer-record r)))]

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

    [(e-join as) #:when (not type) (fail "join expressions not inferrable")]
    [(e-join as) #:when type
     (unless (lattice-type? type)
       (error "cannot join at non-lattice type ~s" (type->sexp type)))
     (for ([a as]) (expr-check a type))
     type]

    ;; ===== ANALYSIS (BUT SOMETIMES SYNTHESIZABLE) EXPRESSIONS =====
    ;;
    ;; we can synthesize these (assuming their subterms synthesize), so we do,
    ;; even though it's non-standard.
    ;;
    ;; TODO: synthesize join expressions when possible
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
       [#f (t-record (hash-map-values expr-check fields))]
       [(t-record field-types)
        ;; we return the inferred type, and the subtype check will ensure it
        ;; has all the necessary fields.
        (t-record (for/hash ([(n e) fields])
                    (define (err) (fail "extra field: ~a" n))
                    (values n (expr-check e (hash-ref field-types e err)))))]
       [_ (fail "record expression must have record type")])]

    [(e-tag name subj)
     (match type
       [#f (t-sum (hash name (expr-check subj)))]
       [(t-sum branches)
        (define (err) (fail "no such branch in sum type: ~a" name))
        (expr-check subj (hash-ref branches name err))
        type]
       [_ (fail "tagged expression must have sum type")])]

    [(e-set '()) #:when (not type) (fail "can't infer type of empty set")]
    [(e-set elems)
     (with-tone 'any
       (match type
         [#f (t-set (foldl1 type-lub (map expr-check elems)))]
         [(t-set a) (for ([elem elems]) (expr-check elem a)) type]
         [_ (fail "set expression must have set type")]))]

    [(e-case _ '()) #:when (not type)
     (fail "can't infer type of case with no branches")]
    [(e-case subj branches)
     ;; TODO: case completeness checking.
     ;;
     ;; TODO: think about when it might be ok not to hide the monotone
     ;; environment when typechecking the case-subject. I think only for
     ;; irrefutable patterns, a la (let p = e in e)?
     (define subj-t (with-tone 'any (expr-check subj #f)))
     ;; it's okay to use 'any here ONLY because we hid the monotone environment
     ;; when checking subj.
     (define check-branch (curry visit-branch 'any subj-t type))
     (define branch-types (map check-branch branches))
     (or type (foldl1 type-lub branch-types))])
  ;; ---------- END BIG GIANT CASE ANALYSIS ----------
  )

;; checks a pattern against a type and returns a hash mapping pattern
;; variables to their types.
;;
;; note that patterns are nonlinear - the same variable may be used multiple
;; times. if it is, this indicates an equality check. for example, (cons x x)
;; matches only pairs of two of the same value.
;;
;; TODO: better error messages - maybe keep a pat-stack, like expr-stack?
;; FIXME: needs to be given the tonicity we're binding variables in.
(define/match (pat-check p t)
  [((p-wild) _) (hash)]
  [((p-var name) t) (hash name t)]
  [((p-lit l) t)
   (if (subtype? t (or (lit-type l) (elab-error "unknown literal type")))
       (hash)
       (elab-error "wrong type when matched against literal"))]
  [((and pat (p-tuple pats)) (t-tuple types)) #:when (length=? pats types)
   (union-pat-envs pat (map pat-check pats types))]
  [((p-tuple _) (t-tuple _)) (elab-error "wrong length tuple pattern")]
  [((p-tuple _) t) (elab-error "not a tuple type: ~s" (type->sexp t))]
  [((p-tag tag pat) (t-sum bs))
   (if (dict-has-key? bs tag)
       (pat-check pat (hash-ref bs tag))
       ;; TODO: this is actually ok, it's just dead code; should warn, not
       ;; error
       (elab-error "(WARNING) no such branch in tagged sum"))]
  [((p-tag _ _) _) (elab-error "not a sum")]
  [((and pat (p-and ps)) t)
   (union-pat-envs pat (map (lambda (p) (pat-check p t)) ps))]
  [((and pat (p-or ps)) t)
   (when (empty? ps)
     (elab-error "or-pattern cannot be empty: ~s" (pat->sexp pat)))
   (define hashes (for/list ([p ps]) (pat-check p t)))
   (define vars (hash-key-set (first hashes)))
   (unless (andmap (lambda (x) (equal? vars (hash-key-set x))) hashes)
     (elab-error "all branches of or-pattern must bind same variables: ~s"
                 (type->sexp pat)))
   (foldl1 (lambda (x y) (hash-union-with x y type-lub)) hashes)]
  [((p-let v body result-p) t)
   ;; FIXME: assumes we're matching with tonicity 'any
   (pat-check result-p (with-var v (hyp 'any t) (expr-check body)))])

(define (union-pat-envs pat hashes)
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
    ;; TODO: as usual, better error message
    (elab-error "pattern variable used multiple times has non-equality type ~s"
                (type->sexp type)))
  type)
