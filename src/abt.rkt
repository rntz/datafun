#lang racket

(require "util.rkt" "ast.rkt")

;; A view represents the top-level of a form.
;; `head' is an abstract value, don't touch it.
;; `args' is a list of abt-arg values, representing the subterms.
(struct abt-view (head args) #:transparent)

;; `vars' is a list of variable names bound in this subterm. don't change it.
;; `term' is the expr.
(struct abt-arg (vars term) #:transparent)

;; turns an abt-view back into an expr.
(define (view->expr a)
  (match-define (abt-view head args) a)
  (apply head (map abt-arg-term args)))

;; turns an expr into an abt-view.
(define (view e)
  (define (V f . as) (abt-view f as))
  (define (A x . vs) (abt-arg vs x))
  (match e
    ;; atoms - exprs w/ no children.
    [(or (e-var _ _) (e-free-var _) (e-lit _) (e-prim _)) (V (lambda () e))]
    [(e-ann t e) (V (curry e-ann t) (A e))]
    [(e-lam var body) (V (curry e-lam var) (A body var))]
    [(e-app f x) (V e-app (A f) (A x))]
    [(e-tuple es) (abt-view e-tuple (map A es))]
    [(e-proj i e) (V (curry e-proj i) (A e))]
    [(e-record fs)
     (define l (sort (hash->list fs) symbol<? #:key car))
     (define (c args)
       (e-record (make-immutable-hash (map cons (map car l) args))))
     (abt-view c (map (compose A cdr) l))]
    [(e-record-merge a b) (V e-record-merge (A a) (A b))]
    [(e-tag tag expr) (V (curry e-tag tag) (A expr))]
    [(e-case subj branches)
     (define (c subj . branch-exprs)
       (e-case subj (for/list ([b branches] [e branch-exprs])
                      (case-branch (case-branch-pat b) e))))
     (abt-view c (cons (A subj)
                       (for/list ([b branches])
                         (match-define (case-branch p e) b)
                         (abt-arg (pat-vars p) e))))]
    [(e-join es) (abt-view e-join (map A es))]
    [(e-set es) (abt-view e-join (map A es))]
    [_ TODO]))
