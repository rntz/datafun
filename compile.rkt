#lang racket

(require "util.rkt" "ast.rkt")

;; contexts Γ are lists of racket identifiers.
(define (compile-expr e Γ)
  (define (r e) (compile-expr e Γ))
  (match e
    [(e-ann _ e) (r e)]
    [(e-var _ i) (list-ref Γ i)]
    [(e-lit l) #`'#,l]
    [(e-prim p) TODO]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(compile-expr body (cons var Γ)))]
    [(e-app f a) #`(#,(r f) #,(r a))]
    [(e-tuple es) #`(list #,(map r es))]
    [(e-proj i e)
     (match i [(? number?) #`(list-ref #,(r e) #,i)]
              [(? symbol?) #`(hash-ref #,(r e) '#,i)])]
    [(e-record fs) TODO]
    [(e-record-merge l r) TODO]
    ;; TODO?: "better" representation for tagged things?
    [(e-tag t e) #`(list '#,t #,(r e))]
    [(e-case subj branches) TODO]
    [(e-join es) TODO]
    [(e-singleton e) #`(set #,(r e))]
    [(e-letin v arg body) TODO]
    [(e-fix var body) TODO]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var ,(r expr)))
         #,(compile-expr body (cons var Γ)))]))
