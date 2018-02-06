#lang racket

(require "util.rkt" "types.rkt")
(provide (all-defined-out))

;; ---------- Literals & primitives ----------
(define (lit? x) (if (lit-type x) #t #f))
(define/contract (lit-type l)
  (-> any/c (or/c #f type?))
  (match l
    [(? boolean?) 'bool]
    [(? exact-nonnegative-integer?) 'nat]
    #;[(? string?) 'str]
    #;[(? null?) '(tuple)]
    [_ #f]))


;; ---------- Expressions ----------
;; For now, a pattern is one of:
;;   (tag CTOR VAR)  -- a constructor applied to a variable.
;;   VAR             -- just a variable
(define-flat-contract pat?
  symbol?
  (list/c 'tag symbol? symbol?))

(define (expr-over expr?)
  (or/c
   ;; ---------- miscellanea ----------
   symbol?                   ;; variables
   (list/c 'the type? expr?) ;; type annotation
   ;;(list/c 'trustme expr?)
   ;; ;; do I need type definitions?
   ;;(list/c 'let-type symbol? type? expr?)

   ;; ---------- base types & primitive operations ----------
   lit?
   (list/c 'if expr? expr? expr?) ;; discrete boolean elimination
   (list/c 'when expr? expr?)     ;; monotone boolean elimination.

   ;; ---------- functions ----------
   (list/c 'lambda symbol? expr?)
   (list/c 'call expr? expr?)

   ;; ----- discrete boxes -----
   (list/c 'box expr?)
   (list/c 'letbox symbol? expr? expr?)
   (list/c 'splitsum expr?)

   ;; ---------- sets, semilattices, fixed points ----------
   (list/c 'set expr?) ;; singleton sets only.
   (cons/c 'lub (listof expr?))
   ;; (for x M N) == ⋁(x ∈ M) N
   (list/c 'for symbol? expr? expr?)
   (list/c 'fix symbol? expr?)

   ;; ---------- tuples & sums ----------
   (cons/c 'cons (listof expr?))
   (list/c 'proj nonnegative-integer? expr?)
   (list/c 'tag symbol? expr?)
   (cons/c 'case (cons/c expr? (listof (list/c pat? expr?))))))

(define-flat-contract expr? (expr-over expr?))


;; ---------- mapping over subexpressions ----------
(define/contract (expr-map f expr)
  (-> procedure? any/c any/c)
  ;; TODO: understand parametric contracts, and why this isn't working.
  ;; eg. uncomment this, run infer.rkt, and try (infer '(lambda x x))
  #;
  (parametric->/c [X Y]
                  (-> (-> X Y) (expr-over X) (expr-over Y)))
  (match expr
    [(? (or/c symbol? lit?) x) x]
    [`(the ,A ,M) `(the ,A ,(f M))]
    [`(lambda ,x ,M) `(lambda ,x ,(f M))]
    [`(letbox ,x ,M ,N) `(letbox ,x ,(f M) ,(f N))]
    [`(for ,x ,M ,N) `(for ,x ,(f M) ,(f N))]
    [`(fix ,x ,M) `(fix ,x ,(f M))]
    [`(proj ,i ,M) `(proj ,i ,(f M))]
    [`(tag ,n ,M) `(tag ,n ,(f M))]
    [`(case ,M (,ps ,Ns) ...)
     `(case ,(f M) ,@(for/list ([p ps] [N Ns]) `(,p ,(f N))))]
    ;; many forms just take a list of expressions.
    [`(,(and oper (or 'set 'lub 'cons 'call 'when 'if 'box)) ,@Ms)
     `(,oper ,@(map f Ms))]))

(define (expr-fold expr func)
  (func (expr-map (lambda (x) (expr-fold x func)) expr)))
