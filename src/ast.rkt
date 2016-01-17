#lang racket

(require (except-in syntax/parse expr) (for-syntax syntax/parse))

(require "util.rkt")
(provide (all-defined-out))

;; Whether a variable/hypothesis, function, etc. is unrestricted, monotone, or
;; antitone.
(define tone? (or/c 'any 'mono 'anti))

;; TODO?: make these types print better under ~a?
(enum type
  (t-bool) (t-nat) (t-str)
  (t-tuple types)
  ;; fields is a hash from field names to types
  (t-record fields)
  ;; branches is a hash from branch names to types
  (t-sum branches)
  (t-fun tone arg result)
  (t-set type))

;; Literals & primitives
(define (lit? x) (if (lit-type x) #t #f))
(define/match (lit-type l)
  [((? boolean?)) (t-bool)]
  [((? exact-nonnegative-integer?)) (t-nat)]
  [((? string?)) (t-str)]
  [((? null?)) (t-tuple '())]
  [(_) #f])

(define (prim? x) (set-member? prims x))
(define prims (list->set '(= <= + - * size print puts ++)))

(enum expr
  ;; ---------- miscellanea ----------
  (e-ann type expr)
  (e-var name)
  ;; let binding. in theory, this is just unary case. but case doesn't account
  ;; for tone yet.
  (e-let tone var expr body)
  ;; this moves all our mono/antitone variables into the unrestricted context.
  (e-trustme expr)

  ;; ---------- base types & primitive operations ----------
  (e-lit value)       ;; literals
  (e-prim prim)       ;; primitive functions

  ;; e-cond is the mono/antitone eliminator for booleans. tone is 'mono or
  ;; 'anti. if 'mono, acts as (when arg body). if 'anti, acts as (unless arg
  ;; body).
  (e-cond tone arg body)   ;; monotone eliminator for booleans

  ;; ---------- sets ----------
  (e-set exprs)
  (e-join-in pat arg body)

  ;; ---------- usl operations ----------
  (e-join exprs)
  (e-fix var body)

  ;; ---------- functions ----------
  ;; bidirectional type inference / elaboration figures out which kind (ordinary
  ;; or monotonic) of lambda / application we meant
  (e-lam var body)
  (e-app func arg)

  ;; ---------- products ----------
  (e-tuple exprs)
  ;; projection index is a nat when projecting from a tuple; a symbol when
  ;; projecting from a record.
  (e-proj index expr)
  ;; fields is a hash from field names (as symbols) to exprs
  (e-record fields)
  ;; TODO?: e-record-project (project a set of fields, like in rel.alg.)
  (e-record-merge left right) ;; merges two records, right-biased.

  ;; ---------- sums ----------
  (e-tag tag expr)
  ;; branches is a list of case-branch structs.
  (e-case subject branches)
  ;; TODO: (e-case-mono subject branches)
  ;;
  ;; NOTE: a difficulty with e-case-mono is we can only case monotonically on
  ;; types of the form (A + B). we cannot, for example, case monotonically on
  ;; bool! because bool has an ordering! ugh.
  )

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

;; ;; commented out b/c unused.
;; (define (pat-vars p)
;;   (match p
;;     [(p-var n) (set n)]
;;     [(or (p-wild) (p-lit _)) (set)]
;;     [(or (p-tag _ p) (p-let _ _ p)) (pat-vars p)]
;;     [(or (p-tuple ps) (p-and ps)) (set-unions (map pat-vars ps))]
;;     [(p-or ps) (set-intersects (map pat-vars ps))]))

;; ;; commented out b/c unused.
;; (define/match (pat-irrefutable? pat type)
;;   [((or (p-wild) (p-var _)) _) #t]
;;   [((p-tuple ps) (t-tuple ts))
;;    (andmap pat-irrefutable? ps ts)]
;;   [((p-tag tag1 p) (t-sum (hash-table tag2 t))) #:when (equal? tag1 tag2)
;;    (pat-irrefutable? p t)]
;;   [((p-let _ _ p) t)
;;    ;; PROBLEM: type inference. ugh.
;;    (pat-irrefutable? p TODO)]
;;   [(_ _) #f])
