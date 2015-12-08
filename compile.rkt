#lang racket

(require "util.rkt" "ast.rkt" "elab.rkt")
(provide compile-expr)

;; our "runtime", of sorts.
(define df-union (curry apply set-unions))
;; side-effecting funs return the empty tuple, '()
(define (df-puts x) (displayln x) '())
(define (df-print x) (println x) '())
(define ((df= x) y) (equal? x y))
(define ((df+ x) y) (+ x y))
(define ((df- x) y) (- x y))
(define ((df* x) y) (* x y))
(define ((df<= x) y) (<= x y))
(define ((df++ x) y) (string-append x y))
(define ((df-subset? x) y) (subset? x y))

;; contexts Γ are lists of racket identifiers.
(define (compile-expr e [Γ '()])
  (define (info) (elab-info e))
  (define (r e) (compile-expr e Γ))
  (match e
    [(e-ann _ e) (r e)]
    [(e-var _ i) (list-ref Γ i)]
    [(e-lit l) #`'#,l]
    [(e-prim p) (compile-prim p (info))]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(compile-expr body (cons var Γ)))]
    [(e-app f a) #`(#,(r f) #,(r a))]
    [(e-tuple es) #`(list #,(map r es))]
    [(e-proj i e)
     (match i [(? number?) #`(list-ref #,(r e) #,i)]
              [(? symbol?) #`(hash-ref #,(r e) '#,i)])]
    [(e-record fs)
     #`(hash #,@(for*/list ([(n e) fs]
                            [x (list #`'#,n (r e))])
                  x))]
    [(e-record-merge a b) #`(hash-union-right #,(r a) #,(r b))]
    ;; TODO?: "better" representation for tagged things?
    [(e-tag t e) #`(list '#,t #,(r e))]
    [(e-case subj branches) TODO]
    [(e-join es) #`(#,(joiner-for (info)) #,@(map r es))]
    [(e-set es) #`(set #,@(map r es))]
    [(e-letin v arg body) TODO]
    [(e-fix var body) TODO]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var ,(r expr)))
         #,(compile-expr body (cons var Γ)))]))

(define (compile-prim p t)
  (match p
    ['= #'equal?]
    ['subset? #'subset?]
    ['+ #'df+] ['* #'df*] ['- #'df-] ['<= #'df<=]
    ['++ #'df++]
    ['puts #'df-puts]
    ['print #'df-print]))

;; produces syntax object which evals to an n-ary joiner function for the given
;; type. (maybe I could just have one "magic" joiner function that examines the
;; runtime type?)
(define (joiner-for t)
  (match t
    [(t-bool) TODO]
    [(t-nat) #'+]
    [(t-fs _) TODO]
    [(t-fun i o) TODO]
    [(t-mono i o) TODO]
    [(t-tuple ts) TODO]
    [(t-record fs) TODO]))
