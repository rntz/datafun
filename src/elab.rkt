#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "types.rkt" "env.rkt")
(provide elab (struct-out hyp))

;; The elaborator generates an info hashtable that maps some exprs to their
;; types. see should-remember-type?, below.

;;; returns (values info-table type-of-expr)
;;; if `type' is #f, we infer the type of `expr'.
;;; otherwise, we check that `expr' has type `type'.
(define (elab root-expr #:type [root-type #f] #:env [root-Γ empty-env])
  ;; we annotate errors with the whole expression for context
  (define (on-err e)
    (error (format "~a
when typechecking expression: ~s" (exn-message e) (expr->sexp root-expr))))

  (parameterize ([elab-info (make-hasheq)]
                 [elab-env root-Γ])
    (define type (with-handlers ([exn:type-error? on-err])
                   (expr-check root-expr root-type)))
    (values (elab-info) type)))

;; Elaboration uses envs mapping bound variables to hyp(othese)s. Hypotheses are
;; annotated with their tones & their types. tones can be:
;; - 'any, for ordinary unrestricted variables
;; - 'mono, for monotone variables
;; - #f, for previously-monotone variables hidden by entry into a constant
;;   expression
(struct hyp (tone type) #:transparent)

(define (env-for-tone tone Γ)
  (match tone
    ['mono (elab-env)]
    ['any (env-map (match-lambda [(hyp (not 'any) t) (hyp #f t)] [x x]) Γ)]
    ;; hilarious hack
    ['trustme (env-map (match-lambda [(hyp 'mono t) (hyp 'any t)] [x x]) Γ)]))

(define-syntax-rule (with-tone tone body ...)
  (parameterize ([elab-env (env-for-tone tone (elab-env))]) body ...))


;;; Helper functions.
(define (prim-type-infer p)
  ((lambda (x) (and x (parse-type x)))
   (match p
     [(or '+ '*) '(nat nat ~> nat)]
     ['- '(nat ~> nat -> nat)]
     ['++ '(str str -> str)]
     ['puts '(str -> (*))]
     [_ #:when (prim? p) #f])))

(define (prim-has-type? p t)
  (define pt (prim-type-infer p))
  (if pt (type=? t pt)
      (match* (p t)
        [('= (t-fun 'any a (t-fun 'any b (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('<= (t-fun 'any a (t-fun _ b (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('subset? (t-fun 'any (t-set a) (t-fun _ (t-set b) (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('size (t-fun _ (t-set a) (t-nat))) (eqtype? a)]
        [('print (t-fun _ _ (t-tuple '()))) #t]
        [(_ _) #f])))

;; whether we need to remember the type of an expression
(define/match (should-remember-type? expr)
  [((or (e-join _) (e-join-in _ _ _) (e-when _ _) (e-fix _ _))) #t]
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


;;; ---------- INTERNALS ----------
;; if `type' is #f, we're inferring.
;; if not, we're checking.
;; returns the type of `expr', which is always be a subtype of `type'.
(define (expr-check expr [type #f])
  (define expr-type (expr-infer expr type))
  (when (should-remember-type? expr)
    (set-info! expr expr-type))
  ;; NB: optimization: could use eq? to avoid call to subtype? here
  (when (and type (not (subtype? expr-type type)))
    ;; TODO: better formatting here
    (type-error
"        expression: ~s
          has type: ~s
but we expect type: ~s"
     (expr->sexp expr) (type->sexp expr-type) (type->sexp type)))
  expr-type)

;; if `type' is #f, we're inferring. if not, we're checking.
(define (expr-infer expr type)
  (define (fail [why #f] . format-args)
    (define message
      (if type
          (format "expression: ~s
cannot be given type: ~s" (expr->sexp expr) (type->sexp type))
          (format "cannot infer type of expression: ~s" (expr->sexp expr))))
    (when why
      (define why-msg (apply format (string-append why) format-args))
      (set! message (string-append message "\nreason: " why-msg)))
    (type-error "~a" message))

  (define (visit-branch tone pat-type body-type branch)
    (match-define (case-branch pat body) branch)
    (with-env (hash-map-values (curry hyp tone) (pat-check pat pat-type))
      (expr-check body body-type)))

  ;; ---------- COMMENCE BIG GIANT CASE ANALYSIS ----------
  (match expr
    ;; ===== SPECIAL CASES FOR INFERRING PRIMITIVES =====
    ;; it would be nice if somehow we didn't need this *and* prim-has-type
    [(e-app (and prim-expr (e-prim (and p (or '= '<= 'subset? 'size 'print))))
            arg)
     (define tone (match p
                    [(or '= '<= 'subset?) 'any]
                    [(or 'size 'print) 'mono]))
     (define arg-type (with-tone tone (expr-check arg)))
     (define result-type (match p
                           ['print (t-tuple '())]
                           ['size (t-nat)]
                           ['= (t-fun 'any arg-type (t-bool))]
                           [(or '<= 'subset?) (t-fun 'mono arg-type (t-bool))]))
     (expr-check prim-expr (t-fun tone arg-type result-type))
     result-type]

    ;; ===== TRANSPARENT / BOTH SYNTHESIS AND ANALYSIS EXPRESSIONS =====
    [(e-trustme e) (with-tone 'trustme (expr-check e type))]

    [(e-let tone var subj body)
     (define subj-t (with-tone tone (expr-check subj)))
     (with-var var (hyp tone subj-t) (expr-check body type))]

    [(e-when subj body)
     (expr-check subj (t-bool))
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
       [(hyp (or 'any 'mono) t) t]
       [(hyp #f _) (fail "~a is a hidden monotone variable" n)])]

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
    [(e-lam _ _) #:when (not type) (fail "lambdas not inferrable")]
    [(e-lam var body) #:when type
     (match-define (t-fun tone a body-type) type)
     (with-var var (hyp tone a)
       (expr-check body body-type))
     type]

    [(e-fix _ _) #:when (not type) (fail "fix expressions not inferrable")]
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

    [(e-set '()) (or type (fail "can't infer type of empty set"))]
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
;; TODO: better error messages
;; FIXME: needs to be given the tonicity we're binding variables in.
(define/match (pat-check p t)
  [((p-wild) _) (hash)]
  [((p-var name) t) (hash name t)]
  [((p-lit l) t)
   (if (subtype? t (or (lit-type l) (type-error "unknown literal type")))
       (hash)
       (type-error "wrong type when matched against literal"))]
  [((and pat (p-tuple pats)) (t-tuple types)) #:when (length=? pats types)
   (union-pat-envs pat (map pat-check pats types))]
  [((p-tuple _) (t-tuple _)) (type-error "wrong length tuple pattern")]
  [((p-tuple _) t) (type-error "not a tuple type: ~s" (type->sexp t))]
  [((p-tag tag pat) (t-sum bs))
   (if (dict-has-key? bs tag)
       (pat-check pat (hash-ref bs tag))
       ;; TODO: this is actually ok, it's just dead code; should warn, not
       ;; error
       (type-error "(WARNING) no such branch in tagged sum"))]
  [((p-tag _ _) _) (type-error "not a sum")]
  [((and pat (p-and ps)) t)
   (union-pat-envs pat (map (lambda (p) (pat-check p t)) ps))]
  [((and pat (p-or ps)) t)
   (when (empty? ps)
     (type-error "or-pattern cannot be empty: s" (pat->sexp pat)))
   (define hashes (for/list ([p ps]) (pat-check p t)))
   (define vars (hash-key-set (first hashes)))
   (unless (andmap (lambda (x) (equal? vars (hash-key-set x))) hashes)
     (type-error "all branches of or-pattern must bind same variables: ~s"
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
    (type-error "pattern variable used multiple times has non-equality type ~s"
                (type->sexp type)))
  type)
