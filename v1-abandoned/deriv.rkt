#lang racket

(require "util.rkt" "types.rkt" "exprs.rkt")

(define (shallow-simplify expr)
  ;; TODO!
  expr)

(define/contract (deriv-lit x)
  (-> lit? expr?)
  (match x
    [(? boolean?) #f]
    [(? exact-nonnegative-integer?) `(cons)]))

(define (deriv root-expr #:env [env (hash)])
  (define env (make-parameter #f))

  ;; currently doesn't use tone. is that right?
  (define-syntax-rule (with-vars ([dx x tone] ...) body ...)
    (let ([dx (gensym (format "d~s" x))] ...)
      (define updates (make-immutable-hash `((,x . ,dx) ...)))
      (parameterize ([env (hash-union-right (env) updates)]) body ...)))

  (define (D expr) (shallow-simplify (Deriv expr)))
  (define (Deriv expr)
   (match expr
     [(? symbol? x) (hash-ref (env) x)]
     [`(the ,A ,M) `(the ,TODO ,(D M))]
     [(? lit? x) (deriv-lit x)]
     [`(if ,M ,N1 ,N2) TODO]
     [`(when ,M ,N) TODO]
     [`(lambda ,x ,M) (with-vars ([dx x 'mono]) `(lambda ,x (lambda ,dx ,(D M))))]
     [`(call ,M ,N) `(call (call ,(D M) ,N) ,(D N))]
     [`(box ,M) `(box ,(D M))]
     [`(letbox ,x ,M ,N) TODO]
     [`(splitsum ,M) `(splitsum ,(D M))]
     [`(set ,_) `(lub)]
     [`(lub ,@Ms) `(lub ,@(map D Ms))]
     [`(for ,x ,M ,N) TODO]
     [`(fix ,x ,M) TODO]
     [`(cons ,@Ms) `(cons ,@(map D Ms))]
     [`(proj ,i ,M) `(proj ,i ,(D M))]
     [`(tag ,n ,M) `(tag ,n ,(D M))]
     [`(case ,M (,ps ,Ns) ...) TODO]
     ))

  (parameterize ([env env]) (D root-expr)))
