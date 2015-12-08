#lang racket

(require (except-in syntax/parse expr) (for-syntax syntax/parse))

(require "util.rkt")
(provide (all-defined-out))

;; TODO: make these types print better under ~a. or maybe use ~v everywhere?
(enum type
  (t-bool) (t-nat) (t-str)
  (t-tuple types)
  ;; fields is a hash from field names to types
  (t-record fields)
  ;; branches is a hash from branch names to types
  (t-sum branches)
  (t-fun arg result)
  (t-mono arg result)
  (t-fs type))

(enum expr
  (e-ann type expr)
  ;; DeBruijn indexing w/ name for readability
  (e-var name index)
  ;; used for literals & primitive functions.
  (e-lit value)
  (e-prim prim)
  ;; bidirectional type inference / elaboration figures out which kind (ordinary
  ;; or monotonic) of lambda / application we meant
  (e-lam var body) (e-app func arg)
  (e-tuple exprs) (e-proj index expr)
  ;; fields is a hash from names to exprs
  (e-record fields)
  (e-record-merge left right) ;; merges two records. right-biased.
  (e-tag tag expr)
  ;; branches is a list of case-branch structs.
  (e-case subject branches)
  ;; TODO: unify e-empty, e-join into one node type
  (e-empty) (e-join left right)
  (e-singleton expr) (e-letin var arg body)
  (e-fix var body)
  ;; let binding. TODO: support pats here?
  ;; kind is either 'any or 'mono.
  (e-let kind var expr body))

(struct case-branch (pat body) #:transparent)

;; TODO: pats for records.
(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag pat)
  (p-lit lit))


;; Convenience macros
(define-syntax-parser Bool [_:id #'(t-bool)])
(define-syntax-parser Nat [_:id #'(t-nat)])
(define-syntax-parser Str [_:id #'(t-str)])
(define-match-expander FS
  (syntax-parser [(_ a) #'(t-fs a)])
  (syntax-parser [(_ a) #'(t-fs a)]))
(define-for-syntax expand->
  (syntax-parser
    [(_ a) #'a]
    [(_ a b ...) #'(t-fun a (-> b ...))]))
(define-match-expander -> expand-> expand->)
(define-for-syntax expand~>
  (syntax-parser
    [(_ a) #'a]
    [(_ a b ...) #'(t-mono a (~> b ...))]))
(define-match-expander ~> expand~> expand~>)
;; TODO: remove × if not sufficiently useful
(define-match-expander ×
  (syntax-parser [(× a ...) #'(t-tuple (list a ...))])
  (syntax-parser [(× a ...) #'(t-tuple (list a ...))]))


;;; Type stuff
(define type=? equal?)

(define (type-wf? x)
  (match x
    [(t-mono a b) (andmap (andf type-wf? lattice-type?) (list a b))]
    [(t-fun a b) (andmap type-wf? (list a b))]
    [(t-fs a) (type-wf? a)]
    [(t-tuple ts) (andmap type-wf? ts)]
    [(t-sum bs) ((hash/c symbol? type-wf? #:immutable #t) bs)]
    [(t-record as) ((hash/c symbol? type-wf? #:immutable #t) as)]
    [_ #t]))

(define (lattice-type? x)
  (match x
    [(or (t-bool) (t-nat) (t-mono _ _) (t-fs _)) #t]
    [(or (t-str) (t-sum _)) #f]
    [(t-tuple ts) (andmap lattice-type? ts)]
    [(t-record as) (andmap lattice-type? (hash-values as))]
    [(t-fun _ r) (lattice-type? r)]))

(define (eqtype? x)
  (match x
    [(or (t-bool) (t-nat) (t-str)) #t]
    [(or (t-record (app hash-values as)) (t-sum (app hash-values as))
         (t-tuple as))
     (andmap eqtype? as)]
    [(or (t-fun _ _) (t-mono _ _)) #f]
    [(t-fs a) (eqtype? a)]))

(define (finite-type? t)
  (match t
    [(t-bool) #t]
    [(t-fs a) (finite-type? a)]
    [(or (t-tuple as)
         (t-record (app hash-values as)) (t-sum (app hash-values as)))
     (andmap finite-type? as)]
    [(or (t-fun a b) (t-mono a b)) (andmap finite-type? (list a b))]
    [_ #f]))

(define (fixpoint-type? t)
  (match t
    [(or (t-bool) (t-nat)) #t]
    [(or (t-tuple as) (t-record (app hash-values as)))
     (andmap fixpoint-type? as)]
    [(t-fs a) (eqtype? a)]
    [_ ((andf finite-type? lattice-type?) t)]))


;;; expression & pattern stuff
(define (pat-vars p)
  (match p
    [(or (p-wild) (p-lit _)) '()]
    [(p-var n) (list n)]
    [(p-tuple ps) (append* (map pat-vars ps))]
    [(p-tag _ p) (pat-vars p)]))


;;; Literals & primitives
(define (lit? x) (if (lit-type x) #t #f))
(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-nat)]
    [(string? l) (t-str)]
    [#t #f]))

(define prims (list->set '(= <= + - * subset? print puts ++)))
(define (prim? x) (set-member? prims x))

(define (prim-type-infer p)
  (match p
    ['<= (-> Nat (~> Nat Bool))]
    [(or '+ '*) (~> Nat Nat Nat)]
    ['- (~> Nat (-> Nat Nat))]
    ['++ (-> Str Str Str)]
    ['puts (~> Str (×))]
    [_ #f]))

(define (prim-has-type? p t)
  (define pt (prim-type-infer t))
  (if pt (type=? t pt)
    (match* (p t)
      [('= (-> a b (t-bool)))
        (and (type=? a b) (eqtype? a))]
      [('subset? (-> (FS a) (~> (FS b) (t-bool))))
        (and (type=? a b) (eqtype? a))]
      [('print (~> _ (×))) #t]
      [(_ _) #f])))
