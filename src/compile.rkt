#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "runtime.rkt")
(provide compile)

;; contexts Γ are envs mapping variables to what they should compile to (an
;; identifier, generally). info maps exprs to elaboration info; see elab.rkt.
(define (compile e #:env Γ #:info info)
  (parameterize ([elab-info info]
                 [compile-env Γ])
    (do-expr e)))


;;; ---------- PARAMETERS ----------
(define elab-info (make-parameter #f))
(define (no-info e) (error "no elab info for: ~s" (expr->sexp e)))
(define (info e [orelse (lambda () (no-info e))])
  (hash-ref (elab-info) e orelse))

(define compile-env (make-parameter #f))
(define-syntax-rule (with-var var id body ...)
  (parameterize ([compile-env (env-bind var id (compile-env))]) body ...))
(define-syntax-rule (with-env more-env body ...)
  (parameterize ([compile-env (env-extend (compile-env) more-env)]) body ...))


;;; ---------- INTERNAL FUNCTIONS ----------
(define (do-expr e)
  (define (join . args) #`(df-join '#,(info e) (list #,@args)))
  (match e
    [(e-ann _ e) (do-expr e)]
    [(e-var n) (env-ref (compile-env) n)]
    [(e-lit l) #`'#,l]
    [(e-prim p) (do-prim p)]
    [(e-lam v body)
     (define var (gensym v))
     #`(lambda (#,var) #,(with-var v var (do-expr body)))]
    [(e-app f a) #`(#,(do-expr f) #,(do-expr a))]
    [(e-tuple es) #`(list #,@(map do-expr es))]
    [(e-proj (? number? i) e) #`(list-ref #,(do-expr e) #,i)]
    [(e-proj (? symbol? i) e) #`(hash-ref #,(do-expr e) '#,i)]
    [(e-record fs)
     #`(hash #,@(for*/list ([(n e) fs]
                            [x (list #`'#,n (do-expr e))])
                  x))]
    [(e-record-merge a b) #`(hash-union-right #,(do-expr a) #,(do-expr b))]
    [(e-tag t e) #`(list '#,t #,(do-expr e))]
    [(e-case subj branches)
     #`(match #,(do-expr subj) #,@(do-case-branches branches))]
    [(e-join es) (apply join (map do-expr es))]
    [(e-set es) #`(set #,@(map do-expr es))]
    [(e-join-in pat arg body)
     #`(for/fold ([acc #,(join)])
                 ([elt #,(do-expr arg)])
         #,(join #'acc
                 #`(match elt
                     #,@(do-case-branches (list (case-branch pat body)))
                     [_ #,(join)])))]
    [(e-cond 'mono subj body) #`(if #,(do-expr subj) #,(do-expr body) #,(join))]
    [(e-cond 'anti subj body) #`(if #,(do-expr subj) #,(join) #,(do-expr body))]
    [(e-fix v body)
     (define var (gensym v))
     #`(df-fix #,(join) (lambda (#,var) #,(with-var v var (do-expr body))))]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var #,(do-expr expr)))
         #,(with-var v var (do-expr body)))]
    [(e-trustme e) (do-expr e)]))

(define (do-case-branches branches)
  (for/list ([b branches])
    (match-define (case-branch pat body) b)
    (define-values (rkt-pat pat-var-ids) (do-pat pat))
    #`[#,rkt-pat #,(with-env pat-var-ids (do-expr body))]))

;; returns (values racket-pattern hash-from-vars-to-idents)
(define (do-pat p)
  (define ids (make-hash))
  (define/match (visit p)
    [((p-wild)) #'_]
    [((p-var x)) #`#,(hash-ref! ids x (lambda () (gensym x)))]
    [((p-tuple ps)) #`(list #,@(map visit ps))]
    [((p-tag tag pat)) #`(list '#,tag #,(visit pat))]
    [((p-lit l)) #`'#,l]
    [((p-and ps)) #`(and #,@(map visit ps))]
    [((p-or ps)) #`(or #,@(map visit ps))]
    [((p-let v body result-pat))
     (define var (gensym v))
     #`(app (lambda (#,var) #,(with-var v var (do-expr body)))
            #,(visit result-pat))])
  (define rkt-pat (visit p))
  (values rkt-pat (freeze-hash ids)))

(define (do-prim p)
  (match p
    ['= #'(curry equal?)]
    ['<= #'df<=]
    ['+ #'df+] ['* #'df*] ['- #'df-]
    ['++ #'df++]
    ['puts #'df-puts]
    ['print #'df-print]
    ['size #'set-count]))
