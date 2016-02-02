#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "runtime.rkt")
(provide compile)

;; `env' is an env (see env.rkt) mapping variables to what they should compile
;; to (an identifier, generally). it also maps type names to their definitions,
;; but we don't care about that during compilation (I think).
;;
;; `info' is a hash mapping exprs to elaboration info; see elab.rkt.
(define (compile expr #:env env #:info info)
  (parameterize ([elab-info info]
                 [compile-env env])
    (do-expr expr)))


;;; ---------- PARAMETERS ----------
(define elab-info (make-parameter #f))
(define (no-info e) (error "no elab info for: ~s" (expr->sexp e)))
(define (info e [orelse (lambda () (no-info e))])
  (hash-ref (elab-info) e orelse))

(define/contract compile-env (parameter/c env?) (make-parameter #f))
(define-syntax-rule (with-var var id body ...)
  (parameterize ([compile-env (env-bind-var var id (compile-env))]) body ...))
(define-syntax-rule (with-env var-hash body ...)
  (parameterize ([compile-env (env-bind-vars var-hash (compile-env))])
    body ...))


;;; ---------- INTERNAL FUNCTIONS ----------
(define (do-expr e)
  (define (lub . args) #`(df-lub '#,(info e) (list #,@args)))
  (match e
    [(e-ann _ e) (do-expr e)]
    [(e-var n) (env-ref-var (compile-env) n)]
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
    [(e-tag t es) #`(list '#,t #,@(map do-expr es))]
    [(e-case subj branches)
     #`(match #,(do-expr subj) #,@(do-case-branches branches))]
    [(e-lub es) (apply lub (map do-expr es))]
    [(e-set es) #`(set #,@(map do-expr es))]
    [(e-map kvs) #`(hash #,@(map do-expr (append* kvs)))]
    [(e-map-for v keys body)
     (define var (gensym v))
     #`(for/hash ([#,var #,(do-expr keys)])
         (values #,var
                 #,(with-var v var (do-expr body))))]
    [(e-map-get d k)
     #`(hash-ref #,(do-expr d) #,(do-expr k) (lambda () #,(lub)))]
    [(e-set-bind pat arg body)
     #`(for/fold ([acc #,(lub)])
                 ([elt #,(do-expr arg)])
         #,(lub #'acc
                #`(match elt
                    #,@(do-case-branches (list (case-branch pat body)))
                    [_ #,(lub)])))]
    [(e-map-bind key-pat value arg body)
     (define value-var (gensym value))
     #`(for/fold ([acc #,(lub)])
                 ([(k #,value-var) #,(do-expr arg)])
         #,(lub #'acc
                #`(match k
                    #,@(with-var value value-var
                         (do-case-branches (list (case-branch key-pat body))))
                    [_ #,(lub)])))]
    [(e-cond 'mono subj body) #`(if #,(do-expr subj) #,(do-expr body) #,(lub))]
    [(e-cond 'anti subj body) #`(if #,(do-expr subj) #,(lub) #,(do-expr body))]
    [(e-fix v body)
     (define var (gensym v))
     #`(df-fix #,(lub) (lambda (#,var) #,(with-var v var (do-expr body))))]
    [(e-let _ v expr body)
     (define var (gensym v))
     #`(let ((#,var #,(do-expr expr)))
         #,(with-var v var (do-expr body)))]
    [(e-let-type _ _ body) (do-expr body)]
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
    [((p-tag tag pats)) #`(list '#,tag #,@(map visit pats))]
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
    ['size #'set-count]
    ['keys #'hash-key-set]
    ['lookup #'df-lookup]))
