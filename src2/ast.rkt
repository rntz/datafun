#lang racket

(require "util.rkt" syntax/parse/define)
(provide (all-defined-out))

;; Maybe this should go in util.rkt?
(define-syntax-rule (define-flat-contract name branches ...)
  (define name (opt/c (flat-rec-contract name (or/c branches ...)))))

;; Whether a variable/hypothesis, function, etc. is unrestricted or monotone.
;; TODO: antitone?
(define-flat-contract tone? 'disc 'mono)
(define-flat-contract base-type? 'bool 'nat 'str)


;; ---------- Types ----------
(define (type-over type?)
  (or/c
   base-type?
   (list/c 'var symbol?) ;; type variables or named types
   (list/c 'box type?)   ;; discrete comonad
   (list/c '-> type? type?)
   ;; product & sum types
   (cons/c '* (listof type?))
   (list/c '+ (hash/c symbol? type? #:immutable #t))
   (list/c 'set type?)))

(define-flat-contract exact-type? (type-over exact-type?))
(define-flat-contract fuzzy-type? '_ (type-over fuzzy-type?))

;; only exact types without free type variables can be lattice types.
(define-flat-contract semilattice-type?
  'bool
  (list/c '-> exact-type? semilattice-type?)
  (cons/c '* (listof semilattice-type?))
  (list/c 'set exact-type?))

;; A typing environment associates variable names with *exact* types.
(define env? (hash/c symbol? exact-type? #:immutable #t))

;; Merges two fuzzy types, if they're compatible. Otherwise, errors.
;; If any argument is exact, the result will be exact and equal to the argument[*],
;; or else an exception will be thrown.
;;
;; [*] It's hard to express this property using Racket contracts (I tried using
;; and/c, but and/c doesn't actually act like an intersection type - it just
;; applies all the contracts in order). I could probably use a dependent
;; contract, but meh.
(define/contract (fuzzy-type-merge A B)
  (-> fuzzy-type? fuzzy-type? fuzzy-type?)
  (match* (A B)
    [(A B) #:when (eq? A B) A]
    [(A '_) A]
    [('_ B) B]
    [(`(-> ,A1 ,A2) `(-> ,B1 ,B2))
     `(-> ,(fuzzy-type-merge A1 B1) ,(fuzzy-type-merge A2 B2))]
    [(`(* ,@as) `(* ,@bs)) #:when (= (length as) (length bs))
     `(* ,@(map fuzzy-type-merge as bs))]
    [(`(+ ,h1) `(+ ,h2))
     ;; sums must have *same* sets of tags. fuzzy type merging has nothing to do
     ;; with subtyping!
     #:when (equal? (hash-keyset h1) (hash-keyset h2))
     `(+ ,(hash-map-vals fuzzy-type-merge h1 h2))]
    ;; TODO: good error messages
    [(_ _) (error (format "cannot unify ~s with ~s" A B))]))

;; Literals & primitives
(define (lit? x) (if (lit-type x) #t #f))
(define/contract (lit-type l)
  (-> any/c (or/c #f exact-type?))
  (match l
    [(? boolean?) 'bool]
    [(? exact-nonnegative-integer?) 'nat]
    [(? string?) 'str]
    #;[(? null?) '(tuple)]
    [_ #f]))


;; ---------- Expressions ----------
;; For now, a pattern is one of:
;;   (tag CTOR (var VAR))  -- a constructor applied to a variable.
;;   (var VAR)             -- just a variable
(define-flat-contract pat?
  (list/c 'tag symbol? (list/c 'var symbol?))
  (list/c 'var symbol?))

(define (expr-over expr?)
  (or/c
   ;; ---------- miscellanea ----------
   symbol?                       ;; variables
   (list/c 'the fuzzy-type? expr?) ;; type annotation
   ;;(list/c 'trustme expr?)
   ;; ;; do I need type definitions?
   ;;(list/c 'let-type symbol? exact-type? expr?)

   ;; ---------- base types & primitive operations ----------
   lit?
   ;; monotone boolean elimination.
   (list/c 'when expr? expr?)

   ;; ---------- functions ----------
   (list/c 'lambda symbol? expr?)
   (list/c 'call expr? expr?)

   ;; ---------- sets, semilattices, fixed points ----------
   (cons/c 'set (listof expr?))
   (cons/c 'lub (listof expr?))
   ;; (for x M N) == ⋁(x ∈ M) N
   (list/c 'for symbol? expr? expr?)
   (list/c 'fix symbol? expr?)

   ;; ---------- tuples & sums ----------
   (cons/c 'cons (listof expr?))
   (list/c 'proj nonnegative-integer? expr?)
   (list/c 'tag symbol? expr?)
   (cons/c 'case (listof (list/c pat? expr?)))))

(define-flat-contract expr? (expr-over expr?))
