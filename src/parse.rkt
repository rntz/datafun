#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for datafun.

(define (reserved-form? x) (set-member? reserved-forms x))
(define reserved-forms
  (list->set '(: empty fn λ cons π proj record record-merge extend-record tag
               quote case join set let fix)))

;; contexts Γ are simple lists of identifiers - used to map variable names to
;; debruijn indices.
(define (parse-expr e Γ)
  ;; (printf "(parse-expr ~v ~v)\n" e Γ)
  (define (r e) (parse-expr e Γ))
  (match e
    [(? prim?) (e-prim e)]
    [(? lit?) (e-lit e)]
    ['empty (e-join '())]
    [(? symbol?) (e-var e (or (index-of e Γ) (error "unbound variable:" e)))]
    [`(: ,t ,e) (e-ann (parse-type t) (r e))]
    [`(fn ,x ,e) (e-lam x (parse-expr e (cons x Γ)))]
    [`(λ ,xs ... ,e)
      (set! e (parse-expr e (append (reverse xs) Γ)))
      (foldr e-lam e xs)]
    [`(cons . ,es) (e-tuple (map r es))]
    [`(,(or 'π 'proj) ,i ,e) (e-proj i (r e))]
    [`(record (,ns ,es) ...) (e-record (for/hash ([n ns] [e es])
                                         (values n (r e))))]
    [`(record-merge ,a ,b) (e-record-merge (r a) (r b))]
    [`(extend-record ,base . ,as) (e-record-merge (r base) (r `(record . ,as)))]
    [(or `(tag ,name ,e) `(',name ,e)) (e-tag name (r e))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (r subj)
        (for/list ([p ps] [e es])
          (set! p (parse-pat p))
          (set! e (parse-expr e (append (reverse (pat-vars p)) Γ)))
          (case-branch p e)))]
    [`(join . ,es) (e-join (map r es))]
    [`(set . ,es) (e-set (map r es))]
    ;; TODO: use declaration parsing here
    [`(let ,x <- ,e in ,body)
      (e-letin x (r e) (parse-expr body (cons x Γ)))]
    [`(fix ,x ,body)
      (e-fix x (parse-expr body (cons x Γ)))]
    [`(let ,x = ,e in ,body)
      (e-let 'any x (r e) (parse-expr body (cons x Γ)))]
    [`(let ,x ^= ,e in ,body)
      (e-let 'mono x (r e) (parse-expr body (cons x Γ)))]
    [`(,f ,as ...)
     (if (reserved-form? f)
         (error "invalid use of form:" e)
         (foldl (flip e-app) (r f) (map r as)))]
    [_ (error "unfamiliar expression:" e)]))

(define (parse-type t)
  (match t
    ['bool (t-bool)]
    ['nat (t-nat)]
    ['str (t-str)]
    [`(* ,as ...) (t-tuple (map parse-type as))]
    [`(record (,ns ,ts) ...)
     (t-record (for/hash ([n ns] [t ts])
                 (values n (parse-type t))))]
    [`(+ (,tags ,types) ...)
      (t-sum (for/hash ([tag tags] [type types])
               (values tag (parse-type type))))]
    ;; TODO: allow type expressions like (foo bar -> baz quux ~> blah),
    ;; meaning (foo bar -> (baz quux ~> bar))
    [`(,as ... -> ,r) (foldr t-fun (parse-type r) (map parse-type as))]
    [`(,as ... ~> ,r) (foldr t-mono (parse-type r) (map parse-type as))]
    [`(fs ,a) (t-fs (parse-type a))]
    [_ (error "unfamiliar type:" t)]))

(define (parse-pat p)
  (match p
    ['_ (p-wild)]
    [(? symbol?) (p-var p)]
    [(? lit?) (p-lit p)]
    [`(cons ,ps ...) (p-tuple (map parse-pat ps))]
    [(or `(tag ,name ,pat) `(',name ,pat))
      (p-tag name (parse-pat pat))]
    [_ (error "unfamiliar pattern:" p)]))


;;; Declaration/definition parsing
;;; TODO: support monotone declarations, which bind a monotone variable.
(struct defn (name type expr) #:transparent)

;; given some defns and an unparsed expr, parses the expr in the appropriate
;; environment and produces an expr which let-binds all the defns in the expr.
(define (let-defns defns e Γ)
  (set! e (parse-expr e (append (reverse (map defn-name defns)) Γ)))
  (for/fold ([e e]) ([d defns])
    (match-define (defn n t body) d)
    (e-let 'any n (e-ann t body) e)))

;; decls are used internally to produce defns, so we can separate type
;; annotations from declarations. we don't parse the expressions or types until
;; we turn them into defns.
(enum decl
  (d-ann name type)
  (d-def name expr))

;; produces a list of defns. for now, we don't support referring to a variable
;; before its definition, not even if you give it a type-signature. also, all
;; recursion must be explicit via `fix'.
(define (parse-decls ds Γ)
  (decls->defns (append* (map parse-decl ds)) Γ))

;; produces a list of decls.
(define (parse-decl d)
  ;; (printf "(parse-decl ~v ~v)\n" d Γ)
  (match d
    [`(: ,(? symbol? name) ,t) (list (d-ann name t))]
    [`(def ,(? symbol? name) ,e) (list (d-def name e))]
    [`(def ,(? symbol? name) ,t ,e)
      (list (d-ann name t) (d-def name e))]
    [`(def (,(? symbol? name) ,(? symbol? args) ...) ,body)
      ;; this is a crude hack
      (list (d-def name `(λ ,@args ,body)))]
    [`(def (,(? symbol? name) ,(? symbol? args) ...) ,t ,body)
      (list
        (d-ann name t)
        ;; same hack here
        (d-def name `(λ ,@args ,body)))]))

;; list of decls -> list of defns
(define (decls->defns ds Γ)
  (define acc '())
  (define type-sigs (make-hash))
  (for ([d ds])
    (match d
      [(d-ann n t) (hash-set! type-sigs n (parse-type t))]
      [(d-def n e)
        (define t (hash-ref type-sigs n #f))
        (unless t (error "no type signature for:" n))
        (set! e (parse-expr e Γ))
        (set! Γ (cons n Γ))
        (set! acc (cons (defn n t e) acc))
        (hash-remove! type-sigs n)]))
  (reverse acc))
