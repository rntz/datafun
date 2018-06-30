#lang racket

(require "v0/util.rkt" racket/hash rackunit)


;;; UTILITIES ;;;
(define (list*/c fst . rest)
  (if (null? rest) (listof fst)
      (cons/c fst (apply list*/c rest))))


;;; TONES and TONE CONTEXTS ;;;
(define-flat-contract tone? 'id 'op 'iso 'path)
(define (vars/c ann) (hash/c symbol? ann #:immutable #t))
(define tones? (vars/c tone?))

(define/contract (tone<=? a b)
  (-> tone? tone? boolean?)
  (match* (a b)
    [('iso _) #t] [(_ 'path) #t]
    [(x x) #t]
    [(_ _) #f]))

(define/contract (tone-meet . tones)
  (->* () #:rest (listof tone?) tone?)
  (match (set->list (set-remove (apply set tones) 'path))
    ['() 'path]
    [(list x) x]
    [_ 'iso]))

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
  (apply hash-union #hash() tones #:combine tone-meet))

(module+ test
  (check-equal? 'path (tone-meet))
  (check-equal? 'iso (tone-meet 'id 'id 'op))
  (for ([x '(id op iso path)])
    (check-equal? x (tone-meet x x))
    (check-equal? x (tone-meet x 'path))
    (check-equal? 'iso (tone-meet x 'iso))))


;;; TYPES ;;;
(define-flat-contract internalized-tone? 'id 'op 'iso)
(define-flat-contract discrete-base-type?)
;; strings are ordered x <= y iff x is a prefix of y.
(define-flat-contract base-type? 'bool 'real 'str)
(define-flat-contract type?
  base-type?
  (list/c internalized-tone? type?)
  (list/c 'set type?)
  (list/c '-> type? type?)
  (cons/c '* (listof type?))
  (list/c '+ (hash/c symbol? type? #:immutable #t)))

(exception bottomless)
(define/contract (bottom tone tp)
  (-> internalized-tone? type? any)
  (match* (tone tp)
    [('id 'bool) #f] [('op 'bool) #t]
    [('id 'str) ""]
    [('id `(set ,A)) (set)]
    [(T `(,(? tone? U) ,A)) (bottom (tone-compose T U) A)]
    [(T `(* ,@As)) (map (curry bottom T) As)]
    [(T `(-> ,A ,B)) (let ([bot (bottom T B)]) (lambda (_) bot))]
    ;; singleton sums. I'm not sure this is a good idea. by adding branches,
    ;; subtyping could turn a "bottom" value into a non-bottom! i.e. now bottom
    ;; isn't covariant!
    [(T `(+ ,(hash-table (name A)))) (hash name (bottom tone A))]
    [(T A) (raise-bottomless (format "type ~s has no bottom at tone ~s" A T))]))

(define (type-pointed? tp)
  (with-handlers ([exn:bottomless? (lambda () #f)])
    (bottom 'id tp)
    #t))

(module+ test
  (check-equal? #f (bottom 'id 'bool))
  (check-equal? '() (bottom 'op '(iso (*))))
  (check-equal? '(() ()) (bottom 'iso '(* (op (*)) (*))))
  (check-equal? (hash 'x "") (bottom 'op '(+ #hash((x . (op str))))))
  (check-exn exn:bottomless? (lambda () (bottom 'op 'str))))


;;; SUBTYPING ;;;
(define/contract (left-adjoint tone)
  (-> internalized-tone? tone?)
  (match tone ['id 'id] ['op 'op] ['iso 'path]))

(define/contract (strip-tone T type)
  (-> internalized-tone? type? (values internalized-tone? type?))
  (match type
    [`(,(? tone? U) ,A) (strip-tone (tone-compose T U) A)]
    [A (values T A)]))

(define (detune type)
  (define-values (T A) (strip-tone 'id type))
  (values (left-adjoint T) A))

(define/contract (subtype A B)
  (-> type? type? tone?)
  (define (fail) (error 'subtype "~s is not a subtype of ~s" A B))
  (match* (A B)
    ;; base cases.
    [(A A) #:when (discrete-base-type? A) 'path]
    [(A A) #:when (base-type? A) 'id]
    ;; tone introduction/elimination
    [(A `(,(? tone? U) ,B)) (tone-compose U (subtype A B))]
    [(`(,(? tone? V) ,A) B) (tone-compose (subtype A B) (left-adjoint V))]
    ;; sets
    [(`(set ,A) `(set ,B)) (subtype A B) 'id]
    ;; distribution over products & sums.
    [(`(* ,@As) `(* ,@Bs)) #:when (length=? As Bs)
     (apply tone-meet (map subtype As Bs))]
    [(`(+ ,@As) `(+ ,@Bs))
     #:when (subset? (hash-keyset As) (hash-keyset Bs))
     (apply tone-meet
            (for/list ([(name A) As])
              (subtype A (hash-ref B name))))]
    ;; function cases
    [(`(-> ,A1 ,B1) `(-> ,A2 ,B2))
     (define dom (subtype A2 A1))
     (define cod (subtype B1 B2))
     (unless (match cod
               ;; TODO: can I simplify this to a single case? THEORY!
               ['path (eq? 'path (tone-compose 'path dom))]
               [_ (tone<=? (left-adjoint cod) dom)])
       (fail))
     cod]
    ;; failure case.
    [(A B) (fail)]))

(module+ test
  ;; TODO: more subtype tests. Property/generative testing might be useful.
  (check-equal? 'id   (subtype 'bool 'bool))
  (check-equal? 'op   (subtype 'bool '(op bool)))
  (check-equal? 'path (subtype '(iso bool) 'bool))
  (check-equal? 'iso  (subtype '(op bool) '(iso bool))))


;;; LITERALS, PATTERNS, and EXPRESSIONS ;;;
(define (lit? x) (if (lit-type x) #t #f))
(define/contract (lit-type l)
  (-> any/c (or/c #f type?))
  (cond
    [(boolean? l) 'bool]
    [(real? l) 'real]
    [(string? l) 'str]
    [(null? l) '(*)]
    [#t #f]))

(define-flat-contracts
  [pat?
   symbol? ;; variable

   ;; I can't handle literal patterns yet because it involves testing equality,
   ;; which uses its argument iso-ly.
   ;lit?
   (list*/c 'tuple expr?)
   (list/c 'tag symbol? expr?)]

  ;; TODO: support set and semilattice expressions
  ;; TODO: fixed points
  ;; TODO: built-in functions, e.g. 'not, '+, 'range
  [infer-expr?
   symbol?                    ;; variable
   lit?                       ;;  literal
   (list/c 'the type? expr?)  ;; type annotation
   (list/c infer-expr? expr?) ;; function application
   ;; TODO: handle more inferrable expressions.
   #;(list/c 'let (list/c (list/c symbol? infer-expr?)) infer-expr?)
   #;(list/c 'if expr? infer-expr? infer-expr?)
   #;(list/c 'when expr? infer-expr?)
   #;(list/c 'tag symbol? infer-expr?)
   #;(list*/c 'tuple infer-expr?)
   #;(list*/c 'case infer-expr? (list/c pat? infer-expr?))
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


;;; TYPE CHECKING ;;;
(define types? (vars/c type?))
(define/contract env (parameter/c types?) (make-parameter #hash()))

(define (typerr msg . vals) (error (apply format msg vals)))
(define (unbound x) (typerr "unbound variable: ~a" x))

(define/contract (infer expr)
  (-> infer-expr? (values type? tones?))
  (match expr
    [(? symbol? x)
     (values (hash-ref (env) x (lambda () (unbound x)))
             (hash x 'id))]
    [(app lit-type A) #:when A (values A #hash())]
    [`(the ,A ,M) (values A (check A M))]
    [`(,M ,N)
     (define-values (M-type M-tones) (infer M))
     (match-define-values (M-tone `(-> ,A ,B)) (detune M-type))
     (define N-tones (check A N))
     (values B (tones-meet (tones-apply M-tone M-tones) N-tones))]))

(define-syntax-rule (with-var x-expr A body ...)
  (let ([x x-expr])
    (define tones (parameterize ([env (hash-set (env) x A)]) body ...))
    (values (hash-ref tones x 'path) (hash-remove tones x))))

(define-syntax-rule (with-vars vars body ...)
  (with-vars-do vars (lambda () body ...)))

(define/contract (with-vars-do vars thunk)
  (-> types? (-> tones?) (values tones? tones?))
  (define tones (parameterize ([env (hash-union-right (env) vars)]) (thunk)))
  (values
   (hash-filter-keys (curry hash-has-key? vars) tones)
   (hash-filter-keys (lambda (x) (not (hash-has-key? vars x))) tones)))

(define/contract (check-pat type pat #:tone [tone 'id])
  (->* (type? pat?) (#:tone internalized-tone?) types?)
  (define-values (T A) (strip-tone tone type))
  (set! tone T)
  (match* (A pat)
    [(A (? symbol? x)) (hash x `(,tone ,A))]
    ;; TODO: literal patterns test for equality, which analyses the subject
    ;; discretely! need some condition relating tone, (subtype B A), and Iso! or
    ;; are we just screwed? think of the inference rules.
    #;
    [(A (app lit-type B)) #:when B
     TODO
     (subtype B A) #hash()]
    [(`(* ,@As) `(tuple ,@Ps)) #:when (length=? As Ps)
     ;; TODO: nonlinear patterns
     (apply hash-union #hash() (map (curry check-pat #:tone tone) As Ps))]
    [(`(+ ,@arms) `(tag ,name ,P)) (=> fail)
     (check-pat (hash-ref arms name (lambda () (fail))) P #:tone tone)]
    [(A P) (typerr "pattern ~s cannot match type ~s" P A)]))

(module+ test
  ;; These tests kinda overspecify: (hash 'x 'real) vs (hash 'x '(id real)).
  ;; Not sure what if anything to do about it.
  (check-equal? #hash() (check-pat 'bool #t))
  (check-equal? (hash 'x '(id real)) (check-pat 'real 'x))
  (check-equal? (hash 'x '(id bool) 'y '(id real))
                (check-pat '(* bool real) '(tuple x y)))

  ;; Tone composition.
  (check-equal? (hash 'x '(id real)) (check-pat '(op (op real)) 'x))
  (check-equal? (hash 'x '(iso real)) (check-pat '(iso (op real)) 'x))

  ;; No nonlinear patterns, for now.
  (check-exn any/c (lambda () (check-pat '(* bool real) '(tuple x x)))))

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
     (define-values (x-tone N-tones) (with-var x M-tp (check expected N)))
     (tones-meet (tones-apply x-tone M-tones) N-tones)]

    [`(if ,M ,N ,O)
     (tones-meet (check '(iso bool) M) (check expected N) (check expected O))]

    [`(when ,M ,N)
     (unless (type-pointed? expected)
       (typerr "cannot use `when` at a type without a bottom"))
     (tones-meet (check 'bool M) (check expected N))]

    [`(lambda (,x) ,M)
     (mustbe `(-> ,A ,B))
     (define-values (x-tone M-tones) (with-var x A (check B M)))
     (unless (tone<=? 'id x-tone)
       (typerr "not used monotonically: ~a" x))
     M-tones]

    [`(tag ,name ,M)
     (mustbe `(+ ,arms))
     (define (uhoh) (typerr "invalid constructor for type"))
     (check (hash-ref arms name uhoh) M)]

    [`(tuple ,@Ms)
     (mustbe `(* ,@As))
     (unless (length=? Ms As) (typerr "tuple has wrong length"))
     (apply tones-meet (map check As Ms))]

    [`(case ,M (,pats ,Ns) ...)
     (define-values (M-type M-tones) (infer M))
     (apply tones-meet
       (for/list ([pat pats] [N Ns])
         (define var-types (check-pat M-type pat))
         (define-values (var-tones N-tones)
           (with-vars var-types (check expected N)))
         (define tone (apply tone-meet (hash-values var-tones)))
         (tones-meet (tones-apply tone M-tones) N-tones)))]

    ;; otherwise, defer to type inference.
    [expr
     (define-values (inferred tones) (infer expr))
     (tones-apply (subtype inferred expected) tones)]))

(define (typecheck tp expr #:env [init-env #hash()])
  (parameterize ([env init-env])
    (if tp
        (begin0 tp (check tp expr))
        (let-values ([(tp tones) (infer expr)]) tp))))


;;; TESTS ;;;
(module+ test
  (define (checks! tp expr)
    (when (infer-expr? expr)
      ;; FIXME: this should be a subtype check, not equality. right?
      ;; can I write a test which fails because of this? if not, why not?
      (check-equal? tp (typecheck #f expr)))
    (check-not-exn (lambda () (typecheck tp expr))))

  (define (fails! tp expr)
    (check-exn any/c (lambda () (typecheck tp expr))))

  ;; Type checking
  (checks! 'bool #t)
  (checks! 'real 2)
  (checks! '(-> bool real) '(lambda (x) 2))
  (checks! '(-> bool bool) '(lambda (x) x))

  (checks! '(iso (-> bool bool))      '(lambda (x) x))
  (checks! '(-> (op bool) (op bool))  '(lambda (x) x))
  (checks! '(-> (iso bool) (op bool)) '(lambda (x) x))

  (fails! '(-> bool (op bool))  '(lambda (x) x))
  (fails! '(-> bool (iso bool)) '(lambda (x) x))

  ;; let
  (checks! 'real '(let ([x 2]) x))
  (checks! '(-> bool bool) '(lambda (x) (let ([y x]) y)))
  (checks! '(-> (op bool) (iso real)) '(let ([x 2]) (lambda (y) x)))

  ;; if & when
  (checks! 'real '(if #t 0 1))
  (checks! 'str '(when #f "foo"))
  (fails!  '(-> bool real) '(lambda (x) (if x 1 0)))
  (checks! '(-> bool str) '(lambda (x) (when x "foo")))

  ;; case. TODO: more tests
  (checks! 'real '(case 2 [x x]))
  (checks! 'bool '(case #t [#t #f] [#f #t]))
  (checks! 'bool '(case (the (* bool real) (tuple #f 7))
                    [(tuple x y) x]))

  ;; TODO: tests for tag, tuple, the, function application.
  )
