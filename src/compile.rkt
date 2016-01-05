#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "runtime.rkt")
(provide compile-expr)

;; contexts Γ are envs mapping variables to what they should compile to (an
;; identifier, generally). info maps exprs to elaboration info; see elab.rkt.
(define (compile-expr e Γ info)
  (define (expr-info)
    (hash-ref info e (lambda () (error "no elab info for: ~s" (expr->sexp e)))))
  (define (r e) (compile-expr e Γ info))
  (match e
    [(e-ann _ e) (r e)]
    [(e-var n) (env-ref Γ n)]
    [(e-lit l) #`'#,l]
    [(e-prim p) (compile-prim p (expr-info))]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(compile-expr body (env-bind v var Γ) info))]
    [(e-app f a) #`(#,(r f) #,(r a))]
    [(e-tuple es) #`(list #,@(map r es))]
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
              (define-values (pat-ids rkt-pat) (compile-pat pat))
              (define body-Γ (env-extend Γ (pat-vars pat) pat-ids))
              #`[#,rkt-pat #,(compile-expr body body-Γ info)]))]
    [(e-join es) #`(#,(joiner-for (expr-info)) #,@(map r es))]
    [(e-set es) #`(set #,@(map r es))]
    [(e-join-in v arg body)
     (define var (gensym v))
     #`(apply #,(joiner-for (expr-info))
              (for/list ([#,var #,(r arg)])
                #,(compile-expr body (env-bind v var Γ) info)))]
    [(e-when subj body)
     #`(if #,(r subj) #,(r body) (#,(joiner-for (expr-info))))]
    [(e-fix v body)
     (define var (gensym v))
     #`(df-fix (#,(joiner-for (expr-info)))
               (lambda (#,var) #,(compile-expr body (env-bind v var Γ) info)))]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var #,(r expr)))
         #,(compile-expr body (env-bind v var Γ) info))]
    [(e-trustme e) (r e)]))

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
    ['= #'(curry equal?)]
    ['subset? #'(curry subset?)]
    ['+ #'df+] ['* #'df*] ['- #'df-] ['<= #'df<=]
    ['++ #'df++]
    ['puts #'df-puts]
    ['print #'df-print]))
