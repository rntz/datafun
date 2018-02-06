#lang racket

;; Implements taking derivatives of datafun terms.
;;
;; Uses elaboration information. Does not produce elaboration information, so we
;; have to re-elaborate. Oh well.
(require "util.rkt" "ast.rkt" "to-sexp.rkt" "types.rkt" "env.rkt")


;;; ========== Parameters ==========
(define elab-info (make-parameter #f))
(define (no-info e) (error "no elab info for:" (expr->sexp e)))
(define (info e [orelse (lambda () (no-info e))])
  (hash-ref (elab-info) e orelse))

;; We use an env mapping source variables to:
;; - their tone (mono, disc, anti). we do not track whether variables are
;;   hidden; the elaborator should have ensured none of those exist.
;; - their derivative variable
;;
;; TODO: What do we map type names to?
(struct var (tone deriv) #:transparent)

(define/contract δ-env (parameter/c env?) (make-parameter #f))
(define-syntax-rule (with-var name tone δname body ...)
  (parameterize ([δ-env (env-bind-var name (var tone δname) (δ-env))])
    body ...))


;;; ========== Derivatives of types ==========
(define/match (Δ t)
  ;; TODO: consider what to do about t-name.
  [((t-name _))     (error "Δ can't handle type variables")]
  [((t-base b))     (match b ['bool 'bool] ['nat 'nat] ['str (t-tuple '())])]
  [((t-tuple ts))   (t-tuple (map Δ ts))]
  [((t-record fs))  (t-record (hash-map-vals Δ fs))]
  [((t-sum bs))     (t-sum (hash-map-vals (curry map Δ) bs))]
  ;; what's the derivative of an antitone function?
  ;; Δ(A ->- B) = Δ(A^op -> B) = []A^op -> Δ(A^op) -> Δ(B)
  ;; = []A -> ??? -> Δ(B)
  ;;
  ;; what is Δ(A^op)? hypothesis: Δ(A)^op. but what are ⊕, ⊖?
  ;; what is δ(e f) when e is antitone?
  ;;
  ;; what are negative changes to (a : {A})? well, subsets of it we remove, of
  ;; course! how are they ordered? well, the zero change is {}. but is this the
  ;; "greatest" antitone change, or the "least"?
  ;;
  ;; the derivative df of an antitone function (f : {A} ->- B)
  ;; should be such that (df x {}) = 0 (f x).
  ;; so as dx grows in the ordinary sense, df x dx grows. hm!
  ;; so maybe Δ(A^op) = ΔA?
  ;;
  ;; we can figure out what Δ(A^op) should be by
  ;; 1. figuring out what it should be for base types
  ;; 2. figuring out what it should be for sets, {A}
  ;; 3. pushing through the ^op at all other types!
  ;;
  ;; Δ(([]A)^op) = Δ([]A)
  ;; Δ((A -> B)^op) = Δ(A^op -> B^op) = []A -> Δ(A^op) -> Δ(B^op)
  ;; Δ((A x B)^op) = Δ(A^op) x Δ(B^op)
  ;; Δ((A + B)^op) = Δ(A^op) = Δ(B^op)
  ;;
  ;; Δ({A}^op) = {A}
  ;;
  ;; Δ(bool^op) = our choice of bool or bool^op
  ;; Δ(nat^op) = ???
  ;; Δ(str^op) = Δ(str) = 1
  [((t-fun 'anti a b))
   (error "cannot take derivative of antitone functions (yet)")]
  [((t-fun o a b))  (t-fun 'disc a (t-fun o (Δ a) (Δ b)))])


;;; ========== Functions ==========
(define (δ e)
  (match e
    [(e-ann t e) (e-ann (Δ t) (δ e))]
    [(e-var n)   (e-var (var-deriv (env-ref-var (δ-env) n)))]
    [(e-lit l)   e]
    [(e-prim p)  (δ-prim p)]
    [(e-lam n body)
     (define δn (gensym n))
     (match-define (t-fun tone _ _) (info e))
     ;; TODO: think about antitone functions
     (when (equal? tone 'anti) TODO)
     ;; FIXME: will this be type-inferrable?
     ;; do we ever need to insert type ascriptions?
     (e-lam n (e-lam δn (with-var n tone δn (δ body))))]
    [(e-app f a) (e-app (e-app (δ f) a) (δ a))]
    ))

(define (δ-prim p) TODO)


;; TODO: define some simple testing functions that use elab.
(require "elab.rkt")

(define test-expr (e-ann (t-fun 'mono (t-base 'nat) (t-base 'nat)) (e-lam 'x (e-var 'x))))

(define (test expr #:type [root-type #f])
  (define-values (expr-info expr-type) (elab expr #:type root-type))
  (printf "type: ~s\n" (type->sexp expr-type))
  (printf "info: ~s\n" expr-info)
  (define deriv (parameterize ([elab-info expr-info]) (δ expr)))
  (printf "deriv: ~s\n" (expr->sexp deriv))
  deriv)

(displayln "hello")
