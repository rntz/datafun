#lang racket

(require "v0/util.rkt" racket/hash)
(define empty-hash (hash))


;;; TONES and TONE CONTEXTS
(define-flat-contract tone? 'id 'op 'iso 'path)
(define (vars/c ann) (hash/c symbol? ann #:immutable #t))
(define tones? (vars/c tone?))

(define/contract (tone<=? a b)
  (-> tone? tone? boolean?)
  (match* (a b)
    [('iso _) #t] [(_ 'path) #t]
    [(x x) #t]
    [(_ _) #f]))

(define/contract (tone-meet a b)
  (-> tone? tone? tone?)
  (match* (a b)
    [('path b) b] [(a 'path) a]
    [(x x) x]
    [(_ _) 'iso]))

(define/contract (tone-compose a b)
  (-> tone? tone? tone?)
  (match* (a b)
    [(_ (or 'iso 'path)) b]
    [((or 'iso 'path) _) a]
    [('id b) b] [(a 'id) a]
    [('op 'op) 'id]))

(define/contract (tones-apply T tones)
  (-> tone? tones? tones?)
  (hash-map-vals (curry tone-compose T) tones))

(define/contract (tones-meet . tones)
  (->* () #:rest (listof tones?) tones?)
  (apply hash-union empty-hash tones #:combine tone-meet))


;; TYPES
(define-flat-contract internalized-tone? 'op 'iso)
(define-flat-contract discrete-base-type?)
(define-flat-contract base-type? 'bool 'real 'str)
(define-flat-contract type?
  base-type?
  (list/c internalized-tone? type?)
  (list/c '-> type? type?)
  ;; product & sum types
  (cons/c '* (listof type?))
  (list/c '+ (hash/c symbol? type? #:immutable #t))
  (list/c 'set type?))

(define type=? equal?)


;; SUBTYPING
(define (left-adjoint tone)
  (match tone ['id 'id] ['op 'op] ['iso 'path]))

(define (demode type [inner-tone 'id])
  (match type
    [`(,(? tone? tone) ,A)
     (demode A (tone-compose (left-adjoint tone) inner-tone))]
    [A (values inner-tone A)]))

(define (subtype A B [tone 'id])
  (define (fail) (error 'subtype "~s is not a subtype of ~s" A B))
  (match* (A B)
    ;; base cases.
    [(A A) #:when (discrete-base-type? A) 'path]
    [(A A) #:when (base-type? A) 'id]
    ;; tone introduction/elimination
    [(A `(,(? tone? U) ,B)) (tone-compose U (subtype A B))]
    [(`(,(? tone? V) ,A) B) (tone-compose (subtype A B) (left-adjoint V))]
    ;; TODO: distribution over products & sums.
    ;; function cases
    [(`(-> ,A1 ,B1) `(-> ,A2 ,B2))
     (define dom (subtype A2 A1))
     (define cod (subtype B1 B2))
     (unless (match cod
               ;; TODO: think about this.
               ['path (eq? 'path (tone-compose 'path dom))]
               [_ (tone<=? (left-adjoint cod) dom)])
       (fail))
     cod]
    ;; TODO: sets.
    ;; failure case.
    [(A B) (fail)]))


;; LITERALS, PATTERNS, and EXPRESSIONS.
(define (lit? x) (if (lit-type x) #t #f))
(define/contract (lit-type l)
  (-> any/c (or/c #f type?))
  (match l
    [(? boolean?) 'bool]
    [(? real?) 'real]
    #;[(? string?) 'str]
    #;[(? null?) '(tuple)]
    [_ #f]))

(define (list*/c fst . rest)
  (if (null? rest) (listof fst)
      (cons/c fst (apply list*/c rest))))

(define-flat-contracts
  [pat?
   symbol? ;; variable
   (cons/c 'tuple (listof expr?))
   (list/c 'tag symbol? expr?)]

  ;; TODO: sets and semilattices
  [infer-expr?
   symbol?                    ;; variable
   lit?                       ;;  literal
   (list/c 'the type? expr?)  ;; type annotation
   (list/c infer-expr? expr?) ;; function application
   ]

  [expr?
   infer-expr?
   (list/c 'let (list/c (list/c symbol? infer-expr?)) expr?)
   (list/c 'if expr? expr? expr?) ;; discrete boolean elimination
   (list/c 'when expr? expr?)     ;; monotone boolean elimination
   (list/c 'lambda (list/c symbol?) expr?)
   (list/c 'tag symbol? expr?)
   (list*/c 'tuple expr?)
   (list*/c 'case infer-expr? (list/c pat? expr?))])


;;; TYPE CHECKING.
(define types? (vars/c type?))
(define/contract env (parameter/c types?) (make-parameter empty-hash))

(define (typerr msg . vals) (error (apply format msg vals)))
(define (unbound x) (typerr "unbound variable: ~a" x))

(define/contract (infer expr)
  (-> infer-expr? (values type? tones?))
  (match expr
    [(? symbol? x)
     (values (hash-ref (env) x (lambda () (unbound x)))
             (hash x 'id))]
    [(app lit-type A) #:when A (values A empty-hash)]
    [`(the ,A ,M) (values A (check A M))]
    [`(,M ,N)
     (define-values (M-type M-tones) (infer M))
     (match-define-values (M-tone `(-> ,A ,B)) (demode M-type))
     (define N-tones (check A N))
     (values B (tones-meet (tones-apply M-tone M-tones) N-tones))]))

(define-syntax-rule (with-var x A body ...)
  (parameterize ([env (hash-set (env) x A)])
    body ...))

(define/contract (check expected expr)
  (-> type? expr? tones?)

  (define-syntax-rule (mustbe pat)
    (match-define pat
     (match expected
       [pat expected]
       [_ (typerr "type has wrong form")])))

  (match expr
    ;; if the type is toned, immediately apply the corresponding intro rule.
    [(app (const expected) `(,(? tone? tone) ,A))
     (tones-apply tone (check A expr))]

    [`(let ([,x ,M]) ,N)
     (define-values (M-tp M-tones) (infer M))
     (define N-tones (with-var x M-tp (check expected N)))
     (define x-tone (hash-ref N-tones x 'path))
     (tones-meet (tones-apply x-tone M-tones) (hash-remove N-tones x))]

    [`(if ,M ,N ,O) (check '(iso bool) M) TODO]
    [`(when ,M ,N) (check 'bool M) TODO]

    [`(lambda (,x) ,M)
     (mustbe `(-> ,A ,B))
     (define tones (with-var x A (check B M)))
     (define x-tone (hash-ref tones x 'path))
     (unless (tone<=? 'id x-tone)
       (typerr "not used monotonically: ~a" x))
     (hash-remove tones x)]

    [`(tag ,tag ,M) TODO]

    [`(tuple ,@Ms)
     (mustbe `(* ,@As))
     (unless (length=? Ms As) (typerr "tuple has wrong length"))
     (apply tones-meet (map check As Ms))]

    [`(case ,M (,pats ,Ns) ...) TODO]

    ;; otherwise, defer to type inference.
    [expr
     (define-values (inferred tones) (infer expr))
     (tones-apply (subtype inferred expected) tones)]))

(define (typecheck tp expr #:env [init-env empty-hash])
  (parameterize ([env init-env])
    (if tp
        (begin0 tp (check tp expr))
        (let-values ([(tp tones) (infer expr)]) tp))))


;; TODO: test cases
(module+ tests
  (require rackunit)

  (define (checks! tp expr)
    (when (infer-expr? expr)
      (check-equal? tp (typecheck #f expr)))
    (check-not-exn (lambda () (typecheck tp expr))))

  (define (fails! tp expr)
    (check-exn any/c (lambda () (typecheck tp expr))))

  (checks! 'bool #t)
  (checks! 'real 2)
  (checks! '(-> bool real) '(lambda (x) 2))
  (checks! '(-> bool bool) '(lambda (x) x))

  (checks! '(iso (-> bool bool))      '(lambda (x) x))
  (checks! '(-> (op bool) (op bool))  '(lambda (x) x))
  (checks! '(-> (iso bool) (op bool)) '(lambda (x) x))

  (fails! '(-> bool (op bool))  '(lambda (x) x))
  (fails! '(-> bool (iso bool)) '(lambda (x) x))

  ;; let expressions
  (checks! 'real '(let ([x 2]) x))
  (checks! '(-> bool bool) '(lambda (x) (let ([y x]) y)))
  (checks! '(-> (op bool) (iso real)) '(let ([x 2]) (lambda (y) x)))
  )
