#lang racket

(require "util.rkt")
(provide (all-defined-out))

(enum type
  (t-bool) (t-nat) (t-str)
  (t-tuple types)
  ;; branches is a hash from branch names to types
  (t-sum branches)
  (t-fun args result)
  (t-mono args result)
  (t-fs type))

(define (type-wf? x)
  (match x
    [(t-mono as b) (andmap (andf type-wf? lattice-type?) (cons b as))]
    [(t-fun as b) (andmap type-wf? (cons b as))]
    [(t-fs a) (type-wf? a)]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-sum bs) ((hash/c symbol? type-wf? #:immutable #t) bs)]
    [_ #t]))

(define (lattice-type? x)
  (match x
    [(or (t-bool) (t-nat) (t-mono _ _) (t-fs _)) #t]
    [(or (t-str) (t-sum _)) #f]
    [(t-tuple ts) (andmap lattice-type? ts)]
    [(t-fun _ r) (lattice-type? r)]))

(define (eqtype? x)
  (match x
    [(or (t-bool) (t-nat) (t-str)) #t]
    [(or (t-tuple as) (t-sum (app hash-values as)))
      (andmap eqtype? as)]
    [(or (t-fun _ _) (t-mono _ _)) #f]
    [(t-fs a) (eqtype? a)]))

(enum expr
  (e-ann expr type)
  (e-var name index)
  ;; used for literals & primitive functions.
  (e-lit value)
  (e-prim prim)
  ;; DeBruijn indexing w/ name for readability
  (e-fun var type body)
  (e-mono var type body)
  (e-app func arg)
  (e-tuple exprs) (e-proj index expr)
  (e-tag tag expr)
  ;; branches is a list of (pat . expr) pairs. TODO: use a struct!
  (e-case subject branches)
  (e-empty) (e-join left right)
  (e-singleton expr) (e-letin var arg body)
  (e-fix var body))

(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag pat)
  (p-lit lit))

(define (lit? x) (if (lit-type x) #t #f))
(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-nat)]
    [(string? l) (t-str)]
    [#t #f]))

(define (prim? x) (member x '(= <= + - * subset? print ++)))

(define (prim-infer-type p)
  (match p
    ['<= (t-fun (list (t-nat) (t-nat)) (t-bool))]
    [(or '+ '*) (t-mono (list (t-nat) (t-nat)) (t-nat))]
    ['- (t-fun (list (t-nat) (t-nat)) (t-nat))]
    [_ #f]))

(define (prim-has-type? p t)
  (define pt (prim-infer-type t))
  (if pt (equal? t pt)
    (match* (p t)
      [(('= (t-fun (list a b) (t-bool))))
        (and (equal? a b) (eqtype? a))]
      [('subset? (t-fun (list (t-fs a) (t-fs b)) (t-bool))
         (and (equal? a b) (eqtype? a)))]
      [('print (t-mono (list a) (t-tuple '()))) #t]
      [('++ (t-fun (list (t-str) ...) (t-str))) #t]
      [_ #f])))
