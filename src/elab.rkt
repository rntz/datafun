#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "types.rkt" "env.rkt")
(provide (all-defined-out))

(define (prim-type-infer p)
  ((lambda (x) (and x (parse-type x)))
   (match p
     ;; TODO?: extend <= to more types?
     ['<= '(nat -> nat ~> bool)]
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
        [('subset? (t-fun 'any (t-set a)
                          (t-fun _ (t-set b) (t-bool))))
         (and (type=? a b) (eqtype? a))]
        [('print (t-fun _ _ (t-tuple '()))) #t]
        [(_ _) #f])))


;; Elaboration uses envs mapping bound variables to hyp(othese)s. Hypotheses are
;; annotated with their tones & their types. tones can be:
;; - 'any, for ordinary unrestricted variables
;; - 'mono, for monotone variables
;; - #f, for previously-monotone variables hidden by entry into a constant
;;   expression
(struct hyp (tone type) #:transparent)

(define (env-hide-mono Γ)
  (env-map (match-lambda [(hyp (not 'any) t) (hyp #f t)] [x x]) Γ))

(define (env-trustme Γ)
  (env-map (match-lambda [(hyp 'mono t) (hyp 'any t)] [x x]) Γ))


;; The elaborator generates an info hashtable that maps some exprs to info about
;; them that is used for compilation:
;;
;; - e-lam, e-app: 'any or 'mono, for ordinary or monotone {lambdas,application}
;; - e-join, e-join-in, e-prim, e-fix: its type
;;
;; TODO: currently the 'any/'mono information is completely unused (see
;; compile.rkt)! should we remove it?

;; whether we need to remember the type of an expression
(define (should-remember-type expr)
  (match expr
    [(or (e-prim _) (e-join _) (e-join-in _ _ _) (e-when _ _) (e-fix _ _)) #t]
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
      (type-error "~a" message))

    ;; ---------- COMMENCE BIG GIANT CASE ANALYSIS ----------
    (match expr
      ;; ===== SPECIAL CASES FOR INFERRING PRIMITIVES =====
      ;; it would be nice if somehow we didn't need this *and* prim-has-type
      [(e-app (and prim-expr (e-prim (and p (or '= 'subset? 'print)))) arg)
       (define mono (match p ['print #t] [(or '= 'subset?) #f]))
       (define arg-type (visit arg #f (if mono Γ (env-hide-mono Γ))))
       (define result-type (match p
                             ['print (t-tuple '())]
                             ['= (t-fun 'any arg-type (t-bool))]
                             ['subset? (t-fun 'mono arg-type (t-bool))]))
       (visit prim-expr (t-fun (if mono 'mono 'any) arg-type result-type) Γ)
       result-type]

      ;; ===== TRANSPARENT / BOTH SYNTHESIS AND ANALYSIS EXPRESSIONS =====
      [(e-trustme e) (visit e type (env-trustme Γ))]

      [(e-let tone var subj body)
       (define subj-Γ (match tone ['mono Γ]      ['any (env-hide-mono Γ)]))
       (define subj-t (visit subj #f subj-Γ))
       (visit body type (env-bind var (hyp tone subj-t) Γ))]

      [(e-when subj body)
       (visit subj (t-bool) Γ)
       (define body-type (visit body type Γ))
       (unless (lattice-type? body-type)
         (fail "cannot join at non-lattice type ~s" (type->sexp body-type)))
       body-type]

      ;; ===== SYNTHESIS-ONLY EXPRESSIONS =====
      ;; we infer these, and our caller checks the inferred type if necessary
      [(e-ann t e) (visit e t Γ) t]
      [(e-lit v) (lit-type v)]

      [(e-var n)
       (match (env-ref Γ n (lambda () (fail "~a is not bound" n)))
         [(hyp (or 'any 'mono) t) t]
         [(hyp #f _) (fail "~a is a hidden monotone variable" n)])]

      [(e-app func arg)
       (match (visit func #f Γ)
         [(t-fun o a b)
          (set-info! expr o)
          (visit arg a (match o ['mono Γ] ['any (env-hide-mono Γ)]))
          b]
         [func-type (fail "applying non-function ~s : ~s"
                          (expr->sexp func) (type->sexp func-type))])]

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
       (match-define (t-fun tone a body-type) type)
       (set-info! expr tone)
       (visit body body-type (env-bind var (hyp tone a) Γ))
       type]

      [(e-fix _ _) #:when (not type) (fail "fix expressions not inferrable")]
      [(e-fix var body) #:when type
       (unless (fixpoint-type? type)
         (fail "cannot calculate fixpoints of type ~s" (type->sexp type)))
       (visit body type (env-bind var (hyp 'mono type) Γ))]

      [(e-join as) #:when (not type) (fail "join expressions not inferrable")]
      [(e-join as) #:when type
       (unless (lattice-type? type)
         (error "cannot join at non-lattice type ~s" (type->sexp type)))
       (for ([a as]) (visit a type Γ))
       type]

      [(e-join-in _ _ _) #:when (not type)
       (fail "join expressions not inferrable")]
      [(e-join-in var arg body) #:when type
       (unless (lattice-type? type)
         (error "cannot join at non-lattice type ~s" (type->sexp type)))
       (define elem-type
         (match (visit arg #f Γ)
           [(t-set a) a]
           ;; TODO: better error message
           [t (fail "iteratee has non-set type ~s" (type->sexp t))]))
       (visit body type (env-bind var (hyp 'any elem-type) Γ))]

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
         [#f (t-set (foldl1 type-lub (for/list ([a elems])
                                       (visit a #f new-Γ))))]
         [(t-set a) (for ([elem elems]) (visit elem a new-Γ)) type]
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
         ;; it's okay to use (hyp 'any) here ONLY because we hid the monotone
         ;; environment when checking subj.
         (define pat-hyps (hash-map-values (curry hyp 'any)
                                           (check-pat Γ pat subj-t)))
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
;; returns hash mapping pattern variables to their types.
(define (check-pat Γ p t)
  (match* (p t)
   [((p-wild) _) (hash)]
   [((p-var name) t) (hash name t)]
   [((p-lit l) t)
    (if (subtype? t (or (lit-type l) (type-error "unknown literal type")))
        (hash)
        (type-error "wrong type when matched against literal"))]
   [((p-tuple pats) (t-tuple types))
    (if (= (length pats) (length types))
        (hash-unions-right (map (curry check-pat Γ) pats types))
        (type-error "wrong length tuple pattern"))]
   [((p-tuple _) _) (type-error "not a tuple")]
   [((p-tag tag pat) (t-sum bs))
    (if (dict-has-key? bs tag)
        (check-pat Γ pat (hash-ref bs tag))
        ;; TODO: this is actually ok, it's just dead code; should warn, not
        ;; error
        (type-error "(WARNING) no such branch in tagged sum"))]
   [((p-tag _ _) _) (type-error "not a sum")]))
