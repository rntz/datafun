#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a simple s-expression syntax for the language.
;; context are simple lists of identifiers.
(define (parse-expr e Γ)
  ;; (printf "(parse-expr ~v ~v)\n" e Γ)
  (define (r e) (parse-expr e Γ))
  (match e
    [(? prim?) (e-prim e)]
    [(? lit?) (e-lit e)]
    ['empty (e-empty)]
    [(? symbol?) (e-var e (or (index-of e Γ) (error "unbound variable:" e)))]
    [`(: ,t ,e) (e-ann (parse-type t) (r e))]
    [`(fn ,x ,e) (e-lam x (parse-expr e (cons x Γ)))]
    [`(λ ,xs ... ,e)
      (set! e (parse-expr e (append (reverse xs) Γ)))
      (foldr e-lam e xs)]
    [`(cons . ,es) (e-tuple (map r es))]
    [(list (or 'π 'proj) i e) (e-proj i (r e))]
    [(or `(tag ,name ,e) `(',name ,e)) (e-tag name (r e))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (r subj)
        (for/list ([p ps] [e es])
          (set! p (parse-pat p))
          (set! e (parse-expr e (append (reverse (pat-vars p)) Γ)))
          (case-branch p e)))]
    ['(join) (e-empty)]
    [`(join . ,es) (foldr1 e-join (map r es))]
    [`(single ,e) (e-singleton (r e))]
    [`(let ,x <- ,e in ,body)
      (e-letin x (r e) (parse-expr body (cons x Γ)))]
    [`(fix ,x ,body)
      (e-fix x (parse-expr body (cons x Γ)))]
    [`(,f ,as ...)
      (foldl (flip e-app) (r f) (map r as))]
    [_ (error "unfamiliar expression:" e)]))

(define (parse-type t)
  (match t
    ['bool (t-bool)]
    ['nat (t-nat)]
    ['str (t-str)]
    [`(* ,as ...) (t-tuple (map parse-type as))]
    [`(+ (,tags ,types) ...)
      (t-sum (for/hash ([tag tags] [type types])
               (values tag (parse-type type))))]
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
