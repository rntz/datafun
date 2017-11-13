#lang racket

(require "util.rkt" "types.rkt" "exprs.rkt")
(provide (all-defined-out))

;; A typing environment associates variable names with "hypotheses".
;; A "hypothesis" is a tone and an exact type.
(define-struct/contract hyp
  ;; #f means "hidden by monotonicity"
  ([tone (or/c tone? #f)]
   [type exact-type?])
  #:transparent)

(define env? (hash/c symbol? hyp? #:immutable #t))

(define/match (tone-in-context ctx-tone var-tone)
  ;; monotone contexts don't change anything
  [('mono x) x]
  ;; discrete variables always stay discrete
  [(_ 'disc) 'disc]
  ;; discrete contexts hide monotone variables
  [('disc 'mono) #f])

(define (env-for-tone ctx-tone env)
  (define/match (update H)
    [((hyp tone A)) (hyp (tone-in-context ctx-tone tone) A)])
  (hash-map-vals update env))


;; work in progress.
(define (infer expr [expected-type '_])
  (type-awarely (lambda (t x) t) expr expected-type))

(define/contract (pat->env pat type)
  (-> pat? exact-type? env?)
  (match* (pat type)
    [((? symbol? x) A) (hash x (hyp 'mono A))]
    [(`(tag ,n ,(? symbol? x)) `(+ ,h)) #:when (hash-has-key? h n)
     (hash x (hyp 'mono (hash-ref h n)))]
    [(_ _) (error "invalid pattern for type:" type)]))


;; It would be nice if our notion of fuzzy types was powerful enough to encode
;; this directly.
(define/contract (expect-sum type [orelse #f])
  (-> fuzzy-type? (or/c '_ (hash/c symbol? fuzzy-type?)))
  (match type
    [`(+ ,h) h]
    ['_ '_]
    [_ (if orelse (orelse) (error "expected a sum type, got:" type))]))

(define (type-awarely func expr [expected-type '_])
  ;; func : (-> exact-type? (expr-over X) X)
  (define env (make-parameter #f))

  (define-syntax-rule (with-env new-env body ...)
    (parameterize ([env (hash-union-right (env) new-env)]) body ...))

  (define-syntax-rule (with-vars ([name tone type] ...) body ...)
    (with-env (make-immutable-hash `((,name . ,(hyp tone type)) ...)) body ...))

  (define-syntax-rule (with-tone tone body ...)
    (parameterize ([env (env-for-tone tone (env))]) body ...))

  (define ((infer expr) expected-type)
    (define (synth A) (fuzzy-type-merge expected-type A))
    ;; For concision, the following code employs some conventions:
    ;;
    ;; 1. Variables A, B, C stand for types.
    ;;
    ;; 2. I suffix variables with `s` if they stand for a list of things. `As`
    ;; is a list of types, for example.
    ;;
    ;; 2. Variables beginning with M, N, O stand for stuff relating to some
    ;; expression.
    ;;
    ;; 3. Given an expression M, the variable `Mf` is (infer M), `Mt` is the
    ;; type of M, and `Ma` is the annotation returned for M by `func`. Ditto for
    ;; Nf, Nt, Na, Mfs, Mts, Mas, etc.
    (match-define `(,type ,expr-anno)
      (match expr
        ;; ----- miscellanea -----
        [(? symbol? x)
         (match-define (hyp tone A)
           (hash-ref (env) x (lambda () (error "unbound variable:" x))))
         (unless ((or/c 'mono 'disc) tone)
           (error "non-monotone use of variable:" x))
         `(,(synth A) ,x)]

        [`(the ,A ,Mf)
         (match-define `(,Mt ,Ma) (Mf (synth A)))
         `(,Mt (the ,A ,Ma))]

        ;; ----- base types & primitive ops -----
        [(app lit-type A) #:when A `(,(synth A) ,expr)]

        [`(if ,Mf ,Nf ,Of)
         (match-define `(bool ,Ma) (with-tone 'disc (Mf 'bool)))
         (match-define `(,Nt ,Na) (Nf expected-type))
         `(,Nt (if ,Ma ,Na ,(cadr (Of Nt))))]

        [`(when ,Mf ,Nf)
         (match-define `(,Nt ,Na) (Nf expected-type))
         (unless (semilattice-type? Nt)
           (error "Cannot use `when` at non-semilattice type:" Nt))
         `(,Nt (when ,(cadr (Mf 'bool)) ,Na))]

        ;; ----- functions -----
        [`(lambda ,x ,Mf)
         (match-define `(-> ,A ,B) (synth '(-> _ _)))
         (unless (exact-type? A)
           (error "cannot infer argument type for lambda expression"))
         (match-define `(,Mt ,Ma) (with-vars ([x 'mono A]) (Mf B)))
         `((-> ,A ,Mt) (lambda ,x ,Ma))]

        [`(call ,Mf ,Nf)
         (match-define `((-> ,A ,B) ,Ma) (Mf `(-> _ ,expected-type)))
         (match-define `(,_ ,Na) (Nf A))
         `(,B (call ,Ma ,Na))]

        ;; ----- discrete boxes -----
        [`(box ,Mf)
         (match-define `(box ,A) (synth `(box _)))
         (match-define `(,Mt ,Ma) (with-tone 'disc (Mf A)))
         `((box ,Mt) (box ,Ma))]

        [`(letbox ,x ,Mf ,Nf)
         (match-define `((box ,A) ,Ma) (Mf '(box _)))
         (match-define `(,Nt ,Na) (with-vars ([x 'disc A]) (Nf expected-type)))
         `(,Nt (letbox ,x ,Ma ,Na))]

        ;;      M : [](A + B)
        ;; ----------------------
        ;; splitsum M : []A + []B
        [`(splitsum ,Mf)
         (match-define `((box ,A) ,Ma)
           (Mf `(box ,(match (expect-sum expected-type)
                        ['_ '_]
                        [h `(+ ,(hash-map-vals (curry fuzzy-type-merge '(box _)) h))]))))
         `(,(+ (hash-map-vals (lambda (x) `(box x)) (expect-sum A)))
           (splitsum ,Ma))]

        ;; ----- sets, semilattices, fix -----
        [`(set ,Mf)
         (match-define `(set ,A) (synth `(set _)))
         (match-define `(,Mt ,Ma) (Mf A))
         `((set ,Mt) (set ,Ma))]

        [`(lub)
         (define A expected-type)
         (unless (exact-type? A) (error "Cannot infer type of bottom"))
         (unless (semilattice-type? A) (error "Bottom cannot have non-semilattice type:" A))
         `(,A (lub))]

        [`(lub ,Mf ,@Mfs)
         (match-define `(,Mt ,Ma) (Mf expected-type))
         (unless (semilattice-type? Mt)
           (error "Cannot take lub at non-semilattice type:" Mt))
         (define Mas (for/list ([f Mfs]) (cadr (f Mt))))
         `(,Mt (lub ,Ma ,@Mas))]

        [`(for ,x ,Mf ,Nf)
         (match-define `((set ,A) ,Ma) (Mf '(set _)))
         (match-define `(,Nt ,Na) (with-vars ([x 'disc A]) (Nf expected-type)))
         (unless (semilattice-type? Nt)
           (error "Cannot take for-lub over non-semilattice type:" Nt))
         `(,Nt (for ,x ,Ma ,Na))]

        [`(fix ,x ,Mf)
         (define A expected-type)
         (unless (exact-type? A) (error "Cannot infer type for fix expression" A))
         (unless (fixpoint-type? A) (error "Cannot use fix at non-semilattice type:" A))
         (match-define `(,_ ,Ma) (with-vars ([x 'mono A]) (Mf A)))
         `(,A (fix ,x ,Ma))]

        ;; ----- tuples & sums -----
        [`(cons ,@Mfs)
         (match-define `(* ,@As) (synth `(* ,@(for/list ([M Mfs]) '_))))
         (match-define `((,Mts ,Mas) ...) (for/list ([A As] [Mf Mfs]) (Mf A)))
         `((* ,@Mts) (cons ,@Mas))]

        [`(proj ,i ,Mf)
         ;; unfortunately it's not possible to propagate the information that M
         ;; is a tuple whose i'th element has type expected-type here, because we
         ;; don't know how *long* the tuple should be. if we had a more general
         ;; notion of fuzzy type, maybe this could work.
         (match (Mf '_)
           [`((* ,@As) ,Ma) #:when (< i (length As))
            `(,(synth (list-ref As i)) (proj ,i ,Ma))]
           [`((* ,@As) ,_) (error "tuple too short:" As)]
           [`(,Mt ,_) (error "projecting from non-tuple:" Mt)])]

        [`(tag ,n ,Mf)
         (define branches
           (match expected-type
             [`(+ ,h) h]
             ['_ (error "cannot infer type for tag expression")]
             [A (error "tag expression cannot have non-sum type:" A)]))
         (define (fail)
           (error "expression's tag is not a member of its type:" expected-type))
         (match-define `(,Mt ,Ma) (Mf (hash-ref branches n fail)))
         (define A (hash-set branches n Mt))
         (unless (exact-type? A) (error "cannot infer other branches of sum type:" A))
         `((+ ,A) (tag ,n ,Ma))]

        [`(case ,Mf (,ps ,Nfs) ...)
         ;; determine type of subject.
         (match-define `(,Mt ,Ma) (Mf '_))

         ;; TODO FIXME: check exhaustiveness
         ;; (define summands
         ;;   (match Mt [`(+ ,h) h]
         ;;             [_ (error "cannot pattern-match on subject of type:" Mt)]))
         ;; (define tags (hash-keyset summands))

         (define type expected-type)
         (define branches-anno
           (for/list ([p ps] [Nf Nfs])
             ;; find the types of the variables bound.
             (with-env (pat->env p Mt)
               (match-define `(,Nt ,Na) (Nf type))
               (set! type Nt)
               `(,p ,Na))))
         `(,type (case ,Ma ,@branches-anno))
         #;
         (match ps
           ;; if it ends with a catch-all case, OK.
           [`(,(tag ,ns ,_) ... (? symbol?) ,@rest)
            (unless (null? rest) (error "unreachable cases"))
            ns]
           ;; otherwise, has to be exhaustive
           [`((tag ,ns ,_) ...)
            (match* (subset? (list->set ns) tags)
              [(#f _) (error "unreachable case branch for type:" Mt)]
              [(_ #f) (error "non-exhaustive cases for type:" Mt)]
              [(#t #t) (void)])])]))

    `(,type ,(func type expr-anno)))

  (parameterize ([env (hash)])
    (car ((expr-fold expr infer) expected-type))))



;; constructs a "type-aware fold" over expressions.
;;
;; ideally, I'd like to make it possible for such a fold to say "please ignore
;; this subexpression" for efficiency, but I'm going to ignore that for the
;; moment. YAGNI!
#;
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
        ;; TODO: tonicity!
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
         (parameterize ([env (TODO (env) x A)])
           (define-values (M-x M-type) (infer M B))
           (values `(lambda ,x ,M-x) `(-> ,A ,M-type)))]

        [`(call ,M ,N)
         (match-define-values (M-x `(-> ,A ,B)) (infer M `(-> _ ,expected-type)))
         (define-values (N-x N-type) (infer N A))
         (values `(call ,M-x ,N-x) B)]

        ;; sets & semilattices
        ;; FIXME: need to handle discreteness!
        [`(set) #:when (not (exact-type? expected-type))
         (error "can't infer type of empty set")]
        [`(set ,@Ms)
         ;; find the expected element type
         (match-define `(set ,A) (merge '(set _)))
         ;; merge the expected element type, and all the inferred types, and
         ;; that's our element type, if it's exact.
         (define M-xs
           (for/list ([M Ms])
             (define-values (M-x M-type) (infer M A))
             (set! A (fuzzy-type-merge A M-type))
             M-x))
         (values `(set ,@M-xs) `(set ,A))]

        [`(lub ,@Ms) TODO]

        ;; bigvee / set elimination
        [`(for ,x ,M ,N)
         (match-define-values (M-x `(set ,A)) (infer M `(set _)))
         (define-values (N-x N-type)
           (parameterize ([env (TODO (env) x A)])
             (infer N expected-type)))
         ;; TODO: check that N-type is a semilattice type
         (values `(for ,x ,M-x ,N-x) N-type)]

        [`(fix ,x ,M)
         (unless (exact-type? expected-type)
           (error "Cannot infer type for fixed point expression"))
         ;; TODO: require expected-type is a semilattice
         (define-values (M-x _)
           (parameterize ([env (TODO (env) x expected-type)])
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
#;
(define/contract (infer expr [type '_])
  (->* (expr?) (fuzzy-type?) exact-type?)
  ((type-awarely (lambda (_ type) type)) expr type))


;; Tests.
(module+ tests
  (require rackunit)

  (test-equal? "2 _" 'nat (infer '2))
  (test-equal? "id nat->nat" '(-> nat nat) (infer '(lambda x x) '(-> nat nat)))
  (test-equal? "id nat->_" '(-> nat nat) (infer '(lambda x x) '(-> nat _)))

  ;; TODO: more tests.
  )
