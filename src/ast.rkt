#lang racket

(require (except-in syntax/parse expr) (for-syntax syntax/parse))

(require "util.rkt")
(provide (all-defined-out))

;; Whether a variable/hypothesis, function, etc. is unrestricted, monotone, or
;; antitone.
(define tone? (or/c 'any 'mono 'anti))
(define base-type? (or/c 'bool 'nat 'str))

;; TODO?: make types, exprs, pats print better under ~a?
(enum type
  (t-name name) ;; types defined by a type decl
  (t-base name)
  (t-tuple types)
  ;; fields is a hash from field names to types
  (t-record fields)
  ;; branches is a hash from branch names to *lists* of types
  (t-sum [branches (hash/c symbol? (listof type?) #:immutable #t)])
  (t-fun tone arg result)
  (t-set type)
  ;; key must be eqtype?
  (t-map key value)
  ;; TODO: flat lattice on a type. (Flat A) = bot <| ... A ... <| top
  ;; (t-flat type)
  )

;; Literals & primitives
(define (lit? x) (if (lit-type x) #t #f))
(define/match (lit-type l)
  [((? boolean?)) (t-base 'bool)]
  [((? exact-nonnegative-integer?)) (t-base 'nat)]
  [((? string?)) (t-base 'str)]
  [((? null?)) (t-tuple '())]
  [(_) #f])

(define prim?
  (or/c '= '<= '+ '- '* 'size 'print 'puts '++ 'strlen 'substr
        'keys 'get 'lookup 'entries))

(enum expr
  ;; ---------- miscellanea ----------
  (e-ann type expr)
  (e-var name)
  ;; let binding. in theory, this is just unary case. but case doesn't account
  ;; for tone yet.
  (e-let tone var expr body)
  ;; type definitions
  (e-let-type name type body)
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
  (e-set-bind pat arg body) ;; \bigvee(pat <- arg) body

  ;; ---------- maps ----------
  (e-map [key-value-exprs (listof (list/c expr? expr?))])
  ;; (e-map-for x keys e) means {k: [k/x]e | k <- keys}
  (e-map-for var key-set body)
  ;; NB: e-map-get is just a special case of e-map-bind!
  ;; although admittedly, one with a fast impl strategy :P
  (e-map-get map key)
  ;; means (lub of `body' for key-pat,value-var in `arg').
  ;; key-pat is unrestricted; value-var is bound monotonically.
  (e-map-bind key-pat value-var arg body)
  ;; other map operations: some builtin functions, and e-lub if the value type
  ;; is a lattice.

  ;; ---------- usl operations ----------
  (e-lub exprs)
  (e-fix var body)

  ;; ---------- functions ----------
  ;; bidirectional type inference / elaboration figures out which kind (ordinary
  ;; or monotonic) of lambda / application we meant
  (e-lam var body)
  (e-app func arg)

  ;; ---------- products (tuples & records) ----------
  (e-tuple exprs)
  ;; projection index is a nat when projecting from a tuple; a symbol when
  ;; projecting from a record.
  (e-proj index expr)
  ;; fields is a hash from field names (as symbols) to exprs
  (e-record fields)
  ;; TODO?: e-record-project (project a set of fields, like in rel.alg.)
  (e-record-merge left right) ;; merges two records, right-biased.

  ;; ---------- sums ----------
  (e-tag tag exprs)
  ;; branches is a list of case-branch structs.
  (e-case subject branches))

(struct case-branch (pat body) #:transparent)

;; TODO: pats for records.
;; TODO?: pats for sets?
(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag [pats (listof pat?)])
  (p-lit lit)
  (p-and pats)
  (p-or pats)
  ;; binds `var' to thing being matched in `body'. the result of `body' is then
  ;; matched against `pat'.
  ;;
  ;; TODO: replace this with equality pattern, p-eq.
  (p-let var body pat))


;; Syntax sugar for types
(define-match-expander T
  (syntax-parser
    #:datum-literals (bool nat str set map * fun -> ~> ->-)
    [(_ (~and base (~or bool nat str))) #'(t-base 'base)]
    [(_ x:id) #'x]
    [(_ (set t))    #'(t-set (T t))]
    [(_ (map k v))  #'(t-map (T k) (T v))]
    [(_ (* t ...))  #'(t-tuple (list (T t) ...))]
    [(_ (fun o a))  #'a]
    [(_ (fun o a r ...)) #'(t-fun o (T a) (T (fun o r ...)))]
    [(_ (-> a ...))      #'(T (fun 'any a ...))]
    [(_ (~> a ...))      #'(T (fun 'mono a ...))]
    [(_ (->- a ...))     #'(T (fun 'anti a ...))])
  (syntax-parser
    #:datum-literals (bool nat str set map * fun -> ~> ->-)
    [(_ (~and base (~or bool nat str))) #'(t-base 'base)]
    [(_ (set t))    #'(t-set (T t))]
    [(_ (map k v))  #'(t-map (T k) (T v))]
    [(_ (* t ...))  #'(t-tuple (list (T t) ...))]
    [(_ (fun o a))  #'(T a)]
    [(_ (fun o a r ...)) #'(t-fun o (T a) (T (fun o r ...)))]
    [(_ (-> a ...))      #'(T (fun 'any a ...))]
    [(_ (~> a ...))      #'(T (fun 'mono a ...))]
    [(_ (->- a ...))     #'(T (fun 'anti a ...))]))


;;; Expression & pattern stuff

;; ;; commented out b/c unused.
;; (define (pat-vars p)
;;   (match p
;;     [(p-var n) (set n)]
;;     [(or (p-wild) (p-lit _)) (set)]
;;     [(or (p-tag _ p) (p-let _ _ p)) (pat-vars p)]
;;     [(or (p-tuple ps) (p-and ps)) (sets-union (map pat-vars ps))]
;;     [(p-or ps) (sets-intersect (map pat-vars ps))]))

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
