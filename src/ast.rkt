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
  ;; tone is 'any, for ordinary functions, or 'mono, for monotone fns
  (t-fun tone arg result)
  (t-set type))

;;; Literals & primitives
(define (lit? x) (if (lit-type x) #t #f))
(define (prim? x) (set-member? prims x))
(define prims (list->set '(= <= + - * subset? print puts ++)))

(enum expr
  (e-ann type expr)
  (e-var name)
  (e-lit value) ;; literals
  (e-prim prim) ;; primitive functions
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
  (e-set exprs)
  (e-join-in pat arg body)
  (e-when arg body) ;; usl eliminator for booleans.
  (e-fix var body)
  ;; let binding. tone is either 'any or 'mono. (in theory, this is just unary
  ;; case. but case doesn't account for tone yet.)
  (e-let tone var expr body)
  ;; this moves all our "monotone" variables into the unrestricted context.
  (e-trustme expr))

(struct case-branch (pat body) #:transparent)

;; TODO: pats for records.
;; TODO?: pats for sets?
(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag pat)
  (p-lit lit)
  (p-and pats)
  (p-or pats)
  ;; binds `var' to thing being matched in `body'. the result of `body' is then
  ;; matched against `pat'.
  (p-let var body pat))


;;; Expression & pattern stuff
;;; NOTE: pat-vars is currently unused
(define (pat-vars p)
  (match p
    [(p-var n) (set n)]
    [(or (p-wild) (p-lit _)) (set)]
    [(or (p-tag _ p) (p-let _ _ p)) (pat-vars p)]
    [(or (p-tuple ps) (p-and ps)) (set-unions (map pat-vars ps))]
    [(p-or ps) (set-intersects (map pat-vars ps))]))

;;; NOTE: pat-irrefutable? is currently unused
(define/match (pat-irrefutable? pat type)
  [((or (p-wild) (p-var _)) _) #t]
  [((p-tuple ps) (t-tuple ts))
   (andmap pat-irrefutable? ps ts)]
  [((p-tag tag1 p) (t-sum (hash-table tag2 t))) #:when (equal? tag1 tag2)
   (pat-irrefutable? p t)]
  [((p-let _ _ p) t)
   ;; PROBLEM: type inference. ugh.
   (pat-irrefutable? p TODO)]
  [(_ _) #f])

(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-nat)]
    [(string? l) (t-str)]
    [#t #f]))
