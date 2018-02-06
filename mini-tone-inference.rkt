#lang racket

(require "src/util.rkt")

(define-flat-contract tone? 'disc 'mono)
(define-flat-contract base-type? 'bool 'nat #;'str
  )

;; Types.
(define-flat-contract type?
  base-type?
  (list/c 'box type?)   ;; discrete comonad
  (list/c '-> type? type?)
  ;; product & sum types
  (cons/c '* (listof type?))
  (list/c '+ (hash/c symbol? type? #:immutable #t))
  (list/c 'set type?))

(define type=? equal?)


;; Literals, patterns, and expressions.
(define (lit? x) (if (lit-type x) #t #f))
(define/contract (lit-type l)
  (-> any/c (or/c #f type?))
  (match l
    [(? boolean?) 'bool]
    [(? exact-nonnegative-integer?) 'nat]
    #;[(? string?) 'str]
    #;[(? null?) '(tuple)]
    [_ #f]))

(define-flat-contract pat?
  symbol? ;; variable
  (cons/c 'cons (listof expr?))
  (list/c 'tag symbol? expr?))

(define-flat-contract expr?
  symbol? ;; variable
  (list/c 'the type? expr?) ;; type annotation.
  (list/c 'let symbol? expr? expr?)
  ;; many instances of this will be inferred. can I infer *all* of them?
  (list/c 'box expr?)

  lit?
  (list/c 'if expr? expr? expr?) ;; discrete boolean elimination
  (list/c 'when expr? expr?)     ;; monotone boolean elimination

  ;; functions
  (list/c 'lambda symbol? expr?)
  (list/c 'call expr? expr?)

  ;; sets, semilattices, fixed points.
  (list/c 'set expr?)
  (cons/c 'lub (listof expr?))
  (list/c 'for symbol? expr? expr?) ;; set elimination
  (list/c 'fix symbol? expr?)

  ;; tuples & sums
  (list/c 'tag symbol? expr?)
  (cons/c 'cons (listof expr?))
  (list/c 'case expr? (listof (list/c pat? expr?))))


;;; TYPE CHECKING/INFERENCE, whee.
;; returns: (values type-inferred hash-of-variable-tones)
(define/contract (check type expr #:env [environ #f])
  (define env (make-parameter #f))

  ;; maybe I should have a monad, where "using a variable w/ a particular tone"
  ;; is a side-effect. this is... kind of like the Writer monad?
  ;;
  ;; so maybe I should write this in Haskell.

  (define (combine-uses . xs) TODO)

  (define (check type expr)
    (match-define `(,inferred ,used) (infer type expr))
    (when (and type (not (type=? type inferred)))
      (error "type error"))
    (values inferred used))

  (define (infer type expr)
    (match expr
      [(? symbol? x)
       `(,(hash-ref (env) x (lambda () (error "unbound variable")))
         ,(hash x 'mono))]
      [`(the ,A ,M) (check A M)]
      [`(if ,M ,N ,O)
       (match-define `(bool ,M-use)
         ;; FIXME: need to handle discreteness!
         (begin TODO (check 'bool M)))
       (match-define `(,N-type ,N-use) (check type N))
       (match-define `(,O-type ,O-use) (check type O))
       (unless (type=? N-type O-type) (error "type error"))
       (values N-type (combine-uses M-use N-use O-use))]
      ))

  (parameterize ((env (or environ (hash))))
    (check type expr)))
