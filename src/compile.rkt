#lang racket

(require "util.rkt" "ast.rkt" "env.rkt" "elab.rkt" "runtime.rkt")
(provide compile-expr)

;; contexts Γ are envs mapping variables to what they should compile to (an
;; identifier, generally).
(define (compile-expr e [Γ empty-env])
  (define (info) (elab-info e))
  (define (r e) (compile-expr e Γ))
  (match e
    [(e-ann _ e) (r e)]
    [(e-free-var n) (env-free-ref Γ n)]
    [(e-var _ i) (env-ref Γ i)]
    [(e-lit l) #`'#,l]
    [(e-prim p) (compile-prim p (info))]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(compile-expr body (env-cons var Γ)))]
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
    [(e-case subj branches)
     #`(match #,(r subj)
         #,@(for/list ([b branches])
              (match-define (case-branch pat body) b)
              (define-values (ids rkt-pat) (compile-pat pat))
              #`[#,rkt-pat #,(compile-expr body (env-extend Γ ids))]))]
    [(e-join es) #`(#,(joiner-for (info)) #,@(map r es))]
    [(e-set es) #`(set #,@(map r es))]
    [(e-letin v arg body)
     (define var (gensym v))
     #`(apply #,(joiner-for (info))
              (for/list ([#,var #,(r arg)])
                #,(compile-expr body (env-cons var Γ))))]
    [(e-fix var body) TODO]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var ,(r expr)))
         #,(compile-expr body (env-cons var Γ)))]))

;; returns (values list-of-idents racket-pattern)
(define (compile-pat p)
  (match p
    [(p-wild) (values '() #'_)]
    [(p-var x) (let ([name (gensym x)])
                 (values (list name) #`#,name))]
    [(p-tuple ps) (for/lists (_is _ps) ([p ps]) (compile-pat p))]
    [(p-tag tag pat)
     (define-values (ids rkt-pat) (compile-pat pat))
     (values ids #`(list '#,tag #,rkt-pat))]
    [(p-lit l) (values '() #`'#,l)]))

(define (compile-prim p t)
  (match p
    ['= #'equal?]
    ['subset? #'subset?]
    ['+ #'df+] ['* #'df*] ['- #'df-] ['<= #'df<=]
    ['++ #'df++]
    ['puts #'df-puts]
    ['print #'df-print]))
