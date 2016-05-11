#lang racket

;; s-expression pretty printers for datafun code.
;;
;; TODO: remove this & replace with either/both:
;; - using source-info to show the source the programmer gave
;; - ML-syntax pretty printer

(require "util.rkt" "ast.rkt" "debug.rkt")
(provide (all-defined-out))

(define loop-form? (or/c 'for 'when 'unless))
(define expr-form?
  (or/c loop-form? 'as 'case 'cons 'extend-record 'fix 'if 'let 'lub 'make-map
        'map 'proj 'quote 'record 'record-merge 'set 'tag 'trustme 'λ 'π))


;;; Expression pretty-printing
(define (expr->sexp e)
  (compact-expr
   (match e
     [(e-var n) n]
     [(e-lit v) v]
     [(e-prim p) p]
     [(e-ann t e) `(as ,(type->sexp t) ,(expr->sexp e))]
     [(e-lam v b) `(λ ,v ,(expr->sexp b))]
     [(e-app f a)
      (let loop ([func f] [args (list a)])
        (match func
          [(e-app f a) (loop f (cons a args))]
          [_ (map expr->sexp (cons func args))]))]
     [(e-tuple es) `(cons ,@(map expr->sexp es))]
     [(e-proj i e) `(π ,i ,(expr->sexp e))]
     [(e-record fs) `(record ,@(for/list ([(n e) fs])
                                 `(,n ,(expr->sexp e))))]
     [(e-record-merge l r) `(record-merge ,(expr->sexp l) ,(expr->sexp r))]
     [(e-tag t es) `(',t ,@(map expr->sexp es))]
     [(e-case subj branches)
      `(case ,(expr->sexp subj)
         ,@(for/list ([b branches])
             (match-define (case-branch pat body) b)
             `(,(pat->sexp pat) ,(expr->sexp body))))]
     [(e-lub '()) 'empty]
     [(e-lub l) `(lub ,@(map expr->sexp l))]
     [(e-set es) `(set ,@(map expr->sexp es))]
     [(e-map kvs) `(map ,@(map (curry map expr->sexp) kvs))]
     [(e-map-get d k) `(get ,(expr->sexp d) ,(expr->sexp k))]
     [(e-map-for x key-set body)
      `(make-map ,x ,(expr->sexp key-set) ,(expr->sexp body))]
     [(e-set-bind pat arg body)
      `(set-bind ,(pat->sexp pat) ,(expr->sexp arg) ,(expr->sexp body))]
     [(e-map-bind key-pat val arg body)
      `(map-bind ,(pat->sexp key-pat) ,val ,(expr->sexp arg)
                 ,(expr->sexp body))]
     [(e-cond 'mono subj body) `(when   ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-cond 'anti subj body) `(unless ,(expr->sexp subj) ,(expr->sexp body))]
     [(e-fix var body) `(fix ,var ,(expr->sexp body))]
     [(e-let tone var expr body)
      `(let ([,tone ,var = ,(expr->sexp expr)])
         ,(expr->sexp body))]
     [(e-let-type name type body)
      `(let ([type ,name = ,(type->sexp type)])
         ,(expr->sexp body))]
     [(e-trustme e) `(trustme ,(expr->sexp e))])))

;; checks whether something "looks like" a set of loop clauses.
;; in:                   ((set 2) for x in X when (< x 3))
;; the loop clauses are:         (for x in X when (< x 3))
(define loop? (cons/c loop-form? any/c))

;; applies syntax sugar to make expressions prettier
(define/match (compact-expr expr)
  [('(lub)) 'empty]
  [(`(case ,cnd [#t ,thn] [#f ,els])) `(if ,cnd ,thn ,els)]
  [(`(let ,decls-1 (let ,decls-2 ,body))) `(let (,@decls-1 ,@decls-2) ,body)]
  [(`(λ ,x (λ . ,rest))) `(λ ,x . ,rest)]
  [(`(fix ,name (lub . ,exprs))) #:when (not (= 1 (length exprs)))
   `(fix ,name ,@exprs)]
  [(`(set-bind ,p ,e ,body))    `(for ,p in ,e ,body)]
  [(`(map-bind ,p ,v ,e ,body)) `(for ,p : ,v in ,e ,body)]
  ;; we compact postfix comprehensions, which is slightly complicated
  [(`((,(and form (or 'when 'unless)) ,cnd ,e) . ,(? loop? clauses)))
   `(,e ,@clauses ,form ,cnd)]
  [(`((,(? (not/c expr-form?) e) . ,(? loop? inner))
      . ,(? loop? outer)))
   `(,e ,@outer ,@inner)]
  [(e) e])


;;; Type pretty-printing
(define (type->sexp t)
  (define (hash->sexps h)
    (for/list ([(name type) h])
      `(,name ,(type->sexp type))))
  (match t
    [(t-name name) name]
    [(t-base name) name]
    [(t-tuple ts) `(* ,@(map type->sexp ts))]
    [(t-record fields)
     `(record ,@(for/list ([(name type) fields])
                  `(,name ,(type->sexp type))))]
    [(t-sum branches)
     `(+ ,@(for/list ([(name types) branches])
             `(,name ,@(map type->sexp types))))]
    [(t-set a) `(set ,(type->sexp a))]
    [(t-map k v) `(map ,(type->sexp k) ,(type->sexp v))]
    [(t-fun tone a b)
     (let loop ([args (list a)] [result b])
       (match result
         [(t-fun tone2 a b) #:when (equal? tone tone2)
          (loop (cons a args) b)]
         [_ `(,@(map type->sexp (reverse args))
              ,(match tone ['disc '->] ['mono '~>] ['anti '->-])
              ,(type->sexp result))]))]))

(define (arrow-type->sexp t)
  (match t
    [(t-fun _ _ _) (type->sexp t)]
    [_ `(,(type->sexp t))]))


;; Pattern pretty-printing
(define (pat->sexp p)
  (match p
    [(p-wild) '_]
    [(p-var x) x]
    [(p-lit x) x]
    [(p-tuple ps) `(cons ,@(map pat->sexp ps))]
    [(p-tag name pats) `(',name ,@(map pat->sexp pats))]
    [(p-or `(,p)) (pat->sexp p)]
    [(p-or pats) `(or ,@(map pat->sexp pats))]
    [(p-and `(,p)) (pat->sexp p)]
    [(p-and pats) `(and ,@(map pat->sexp pats))]
    [(p-eq e) `(= ,(expr->sexp e))]))

