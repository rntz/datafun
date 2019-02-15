#lang racket

;; NOTE:
;;
;; New idea is to only propagate exactly the type information I need for each
;; compilation step, rather than trying to either bidirectionally infer at each
;; step (which either involves lots of boilerplate or thinking hard about
;; tagless-final) or type annotate enough that everything is inferrable.
;;
;; So, what type information do I need?
;;
;; 1. Semilattice operators (⊥, ∨, for) need to know the semilattice structure
;; they're using. Doesn't need the whole type (eg. set union is the same
;; structure regardless of element type).
;;
;; 2. Need to compute 0-changes in δ(for) and φ(for). However, this doesn't
;; really require the type, as it can be computed dynamically from the value. In
;; fact, we _have_ to compute it dynamically from the value for sum types, since
;; 0 (inl x) = inl (0 x) ≠ inr (0 x) = 0 (inr x).
;;
;; OTOH, couldn't I _define_ (inr dx) to be a zero-change for (inl x) values?
;; Hm!

;; ALTERNATIVE STRATEGY
;;
;; Pass types everywhere (w/ annotations where checking isn't sufficient), but
;; do everything final-style?

(require "util.rkt")


;; Language
(define var? symbol?)

;; A ::= {A} | []A | A x B | A + B | A -> B
;; except we make functions & products n-ary.
(define-flat-contract type?
  `(set ,type?)
  `(□ ,type?)
  `(× ,@(listof type?))
  `(+ ,type? ,type?)
  ;; return type comes first, hence the reverse arrow. arguments are
  ;; left-to-right, though.
  `(<- ,type? ,@(listof type?)))

;; Type-annotated expressions.
(define-flat-contract expr?
  var?
  `(fix ,expr?)
  `(fastfix ,expr?)
  ;; sets
  `(set ,expr?)
  `(bot ,type?)
  `(vee ,expr? ,expr?)
  `(for ,var? ,expr? ,expr?)
  ;; boxes
  `(box ,expr?)
  `(letbox ,var? ,expr? ,expr?)
  `(split ,expr?)
  ;; products
  `(cons ,@(listof expr?))
  `(pi ,natural? ,expr?)
  ;; sums
  `(inl ,expr?) `(inr ,expr?)
  `(case ,expr? [,var? ,expr?] [,var? ,expr?])
  ;; functions
  `(lambda ,(listof (list/c var? type?)) ,expr?)
  `(@ ,expr? ,@(listof expr?)))


;; Type translations
(define/contract (Φ type)
  (-> type? type?)
  (match type
    [`(set ,A) `(set ,(Φ A))]
    [`(□ ,A) `(□ (× ,(Φ A) ,(Δ A)))]
    [`(,(and op (or '× '+ '<-)) ,@As) `(,op ,@(map Φ As))]))

(define/contract (Δ type)
  (-> type? type?)
  (match type
    [`(set ,A) `(set ,(Φ A))]
    [`(□ ,A) `(□ ,(Δ A))]
    [`(,(and op (or '× '+)) ,@As) `(,op ,@(map Δ As))]
    [`(<- ,B ,@As)
     `(<- ,(Δ B) ,@(let*/list ([A As]) `((□ ,(Φ A)) ,(Δ A))))]))


;; A convenient hack.
(define δ-vars (make-weak-hasheq))
(define (δ-var x)
  (hash-ref! δ-vars x (gensym (format "d~a" x))))

;; φ([M]) = [φM, δM]
;; φ(let [x] = M in N) = let [x,dx] = φM in φN
(define/contract (φ expr)
  (-> expr? expr?)
  (match expr
    ;; φx = x
    [(? var? x) x]
    ;; φ(fix M) = fastfix φM
    [`(fix ,M) `(fastfix ,(φ M))]
    [`(fastfix ,_) (error "fastfix in source")]
    ;; φ{M} = {φM}
    [`(set ,M) `(set ,(φ M))]
    ;; φ⊥ = ⊥
    [`(bot ,A) `(bot ,(Φ A))]
    ;; φ(M ∨ N) = φM ∨ ΦN
    [`(vee ,M ,N) `(vee ,(φ M) ,(φ N))]
    ;; φ(for (x ∈ M) N) = for (x ∈ φM) let dx = 0 x in φN
    [`(for ,x ,M ,N)
     `(for ,x ,M ,TODO)]
    ;; φ(λx. M) = λx. φM
    [`(lambda ,xtps ,M)
     `(lambda ,(map (match-lambda [`(,x ,A) `(,x ,(Φ A))]) xtps) ,(φ M))]
    ;; φ(M N) = φM φM
    [`(@ ,M ,@Ns) `(@ ,(φ M) ,@(map φ Ns))]
    ))

;; ;; Type-annotated expressions.
;; (define-flat-contract expr?
;;   var?
;;   `(fix ,expr?)
;;   `(fastfix ,expr?)
;;   ;; sets
;;   '(set ,@(listof expr?))
;;   '(vee ,@(listof expr?))
;;   '(for ,var ,expr? ,expr?)
;;   ;; boxes
;;   `(box ,expr?)
;;   `(letbox ,var? ,expr? ,expr?)
;;   `(split ,expr?)
;;   ;; products
;;   `(cons ,@(listof expr?))
;;   `(pi ,natural? ,expr?)
;;   ;; sums
;;   `(inl ,expr?) `(inr ,expr?)
;;   `(case ,expr? [,var? ,expr?] [,var? ,expr?])
;;   ;; functions
;;   `(lambda ,(listof (list/c var? type?)) ,expr?)
;;   `(@ ,expr? ,@(listof expr?)))

(define/contract (δ expr)
  (-> expr? expr?)
  (match expr
    [(? var? x) (δ-var x)]
    [_ TODO]))
