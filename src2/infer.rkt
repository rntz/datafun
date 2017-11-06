#lang racket

(require racket/contract/parametric)
(require "util.rkt" "ast.rkt")
(provide (all-defined-out))


;; constructs a "type-aware fold" over expressions.
;;
;; ideally, I'd like to make it possible for such a fold to say "please ignore
;; this subexpression" for efficiency, but I'm going to ignore that for the
;; moment. YAGNI!
(define/contract (type-awarely func)
  ;; TODO: explain this type/contract.
  (parametric->/c [X]
    (-> (-> (expr-over X) exact-type? X)
        (-> expr? fuzzy-type? X)))

  (define env (make-parameter #f))

  (define (infer expr expected-type)
    (define (merge A) (fuzzy-type-merge A expected-type))

    (define-values (annotated-expr inferred-type)
      (match expr
        ;; variables
        [(? symbol? x)
         (values x (merge (hash-ref (env) x (lambda () (error "unbound variable:" x)))))]

        ;; type annotation
        [`(the ,A ,M)
         (define-values (M-x M-type) (infer M (merge A)))
         (values `(the ,A ,M-x) M-type)]

        ;; literals
        [(app lit-type A) #:when A (values expr (merge A))]

        ;; monotone boolean elimination
        [`(when ,M ,N)
         (match-define-values (M-x 'bool) (infer M 'bool))
         (define-values (N-x N-type) (infer N expected-type))
         ;; TODO: check that N-type is a semilattice type
         (values `(when ,M-x ,N-x) N-type)]

        ;; functions
        [`(lambda ,x ,M)
         (define-values (A B)
           (match expected-type
             [`(-> ,A ,B) #:when (exact-type? A) (values A B)]
             [`(-> ,A ,B) (error "I can't type-check a lambda with an incomplete argument type:" A)]
             [_ (error "I don't know what type to give this lambda expression")]))
         (parameterize ([env (hash-set (env) x A)])
           (define-values (M-x M-type) (infer M B))
           (values `(lambda ,x ,M-x) `(-> ,A ,M-type)))]

        [`(call ,M ,N)
         (match-define-values (M-x `(-> ,A ,B)) (infer M `(-> _ ,expected-type)))
         (define-values (N-x N-type) (infer N A))
         (values `(call ,M-x ,N-x) B)]

        ;; sets & semilattices
        [`(set ,@Ms) TODO]

        [`(lub ,@Ms) TODO]

        ;; bigvee / set elimination
        [`(for ,x ,M ,N)
         (match-define-values (M-x `(set ,A)) (infer M `(set _)))
         (define-values (N-x N-type)
           (parameterize ([env (hash-set (env) x A)])
             (infer N expected-type)))
         ;; TODO: check that N-type is a semilattice type
         (values `(for ,x ,M-x ,N-x) N-type)]

        [`(fix ,x ,M)
         (unless (exact-type? expected-type)
           (error "Cannot infer type for fixed point expression"))
         ;; TODO: require expected-type is a semilattice
         (define-values (M-x _)
           (parameterize ([env (hash-set (env) x expected-type)])
             (infer M expected-type)))
         (values `(fix ,x ,M-x) expected-type)]

        ;; tuples & sums
        [`(cons ,@Ms)
         (define As (match expected-type
                      ['_ (for ([M Ms]) '_)]
                      [`(* ,@As) As]
                      [_ (error "Bad type for tuple expression:" expected-type)]))
         (unless (length=? Ms As)
           (error "Wrong-length tuple:" expected-type))
         (define-values (M-xs M-types)
          (for/lists (M-xs M-types) ([M Ms] [A As]) (infer M A)))
         (values `(cons ,@M-xs) `(* ,@M-types))]

        ;; unfortunately it's not possible to propagate the information that M
        ;; is a tuple whose i'th element has type expected-type here, because we
        ;; don't know how *long* the tuple should be. if we had a more general
        ;; notion of fuzzy type, maybe this could work.
        [`(proj ,i ,M)
         (define-values (M-x M-type) (infer M '_))
         (match M-type
           [`(* ,@As) #:when (< i (length As)) (list-ref As i)]
           [`(* ,@As) (error "tuple too short:" As)]
           [_ (error "projecting from non-tuple:" M-type)])]

        [`(tag ,name ,M) TODO]

        [`(case ,subject ,@branches)
         (define-values (subject-x subject-type) (infer subject '_))
         TODO]))

    (values (func annotated-expr inferred-type) inferred-type))

  (lambda (expr expected-type)
    (define-values (X type)
      (parameterize ([env (hash)]) (infer expr expected-type)))
    X))


;; Infers/checks an expression's type.
(define/contract (infer expr [type '_])
  (->* (expr?) (fuzzy-type?) exact-type?)
  #;(-> expr? fuzzy-type? exact-type?)
  ((type-awarely (lambda (_ type) type)) expr type))


;; Tests.
(module+ tests
  (require rackunit)

  (test-equal? "2 _" 'nat (infer '2))
  (test-equal? "id nat->nat" '(-> nat nat) (infer '(lambda x x) '(-> nat nat)))
  (test-equal? "id nat->_" '(-> nat nat) (infer '(lambda x x) '(-> nat _)))

  ;; TODO: more tests.
  )
