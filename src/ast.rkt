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
  ;; TODO?: e-record-project (project a set of fields, like in rel.alg.)
  (e-record-merge left right) ;; merges two records, right-biased.
  (e-tag tag expr)
  ;; branches is a list of case-branch structs.
  (e-case subject branches)
  ;; TODO: (e-case-mono subject branches)
  (e-join exprs)
  ;; TODO: rename e-letin to e-join-in, or something
  (e-set exprs) (e-letin var arg body)
  (e-fix var body)
  ;; let binding. TODO: support pats here?
  ;; kind is either 'any or 'mono.
  (e-let kind var expr body))

(struct case-branch (pat body) #:transparent)

;; TODO: pats for records.
;; TODO?: pats for sets?
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


;;; Expression & pattern stuff
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
