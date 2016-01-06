#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "runtime.rkt")
(provide compile-expr)

;; contexts Γ are envs mapping variables to what they should compile to (an
;; identifier, generally). info maps exprs to elaboration info; see elab.rkt.
(define (compile-expr e Γ info)
  (define (joiner) (joiner-for (hash-ref info e no-info)))
  (define (no-info) (error "no elab info for: ~s" (expr->sexp e)))

  (define (r e) (compile-expr e Γ info))
  (define (compile-case-branches branches)
    (for/list ([b branches])
      (match-define (case-branch pat body) b)
      (define-values (rkt-pat pat-var-ids) (compile-pat pat))
      (define body-Γ (env-extend Γ pat-var-ids))
      #`[#,rkt-pat #,(compile-expr body body-Γ info)]))

  (match e
    [(e-ann _ e) (r e)]
    [(e-var n) (env-ref Γ n)]
    [(e-lit l) #`'#,l]
    [(e-prim p) (compile-prim p)]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(compile-expr body (env-bind v var Γ) info))]
    [(e-app f a) #`(#,(r f) #,(r a))]
    [(e-tuple es) #`(list #,@(map r es))]
    [(e-proj (? number? i) e) #`(list-ref #,(r e) #,i)]
    [(e-proj (? symbol? i) e) #`(hash-ref #,(r e) '#,i)]
    [(e-record fs)
     #`(hash #,@(for*/list ([(n e) fs]
                            [x (list #`'#,n (r e))])
                  x))]
    [(e-record-merge a b) #`(hash-union-right #,(r a) #,(r b))]
    [(e-tag t e) #`(list '#,t #,(r e))]
    [(e-case subj branches)
     #`(match #,(r subj) #,@(compile-case-branches branches))]
    [(e-join es) #`(#,(joiner) #,@(map r es))]
    [(e-set es) #`(set #,@(map r es))]
    [(e-join-in pat arg body)
     #`(for/fold ([acc (#,(joiner))])
                 ([elt #,(r arg)])
         (#,(joiner) acc
           (match elt
             #,@(compile-case-branches (list (case-branch pat body)))
             [_ (#,(joiner))])))]
    [(e-when subj body) #`(if #,(r subj) #,(r body) (#,(joiner)))]
    [(e-fix v body)
     (define var (gensym v))
     #`(df-fix (#,(joiner))
               (lambda (#,var) #,(compile-expr body (env-bind v var Γ) info)))]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var #,(r expr)))
         #,(compile-expr body (env-bind v var Γ) info))]
    [(e-trustme e) (r e)]))

;; returns (values racket-pattern hash-from-vars-to-idents)
(define (compile-pat p)
  (define ids (make-hash))
  (define (gen-id! name)
    (define v (gensym name))
    (hash-set! ids name v)
    v)
  (define/match (visit p)
    [((p-wild)) #'_]
    [((p-var x)) #`#,(gen-id! x)]
    [((p-tuple ps)) #`(list #,@(map visit ps))]
    [((p-tag tag pat)) #`(list '#,tag #,(visit pat))]
    [((p-lit l)) #`'#,l]
    [((p-and ps)) #`(and #,@(map visit ps))]
    [((p-or ps)) #`(or #,@(map visit ps))]
    [((p-app e p))
     ;; NEED TO BE ABLE TO COMPILE EXPRESSIONS
     TODO])
  (define rkt-pat (visit p))
  (values rkt-pat (freeze-hash ids)))

(define (compile-prim p)
  (match p
    ['= #'(curry equal?)]
    ['subset? #'(curry subset?)]
    ['+ #'df+] ['* #'df*] ['- #'df-] ['<= #'df<=]
    ['++ #'df++]
    ['puts #'df-puts]
    ['print #'df-print]))
