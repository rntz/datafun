#lang racket
(require (only-in racket/hash hash-union))

(define tone? (or/c 'id 'box 'op 'dia))
(define (todo) (error 'todo))

(define/match (subtone? t u)
  [('box _) #t]
  [(_ 'dia) #t]
  [(t u) #:when (equal? t u) #t]
  [(_ _) #f])

(define/match (tone-meet t u)
  [(t u) #:when (subtone? t u) t]
  [(t u) #:when (subtone? u t) u]
  [(_ _) 'box])

(define/match (tone* t u) ; tone composition
  [('id u) u]
  [(t 'id) t]
  [('op 'op) 'id]
  [(_ 'box) 'box] [(_ 'dia) 'dia]
  [('box _) 'box] [('dia _) 'dia])

(define/match (tone-left-adjoint t)
  [('id) 'id] [('op) 'op] [('box) 'dia]
  [('dia) (error 'tone-left-adjoint "dia has no left adjoint")])

(define usage? (hash/c symbol? tone? #:immutable #t #:flat? #t))
(define/contract (usage-scale t usage)
  (-> tone? usage? usage?)
  (for/hash ([(name u) usage]) (values name (tone* t u))))
(define/contract (usage-meet u1 u2)
  (-> usage? usage? usage?)
  (hash-union u1 u2 #:combine tone-meet))

(define type?
  (flat-rec-contract type?
   (or/c
    'num
    'bool
    symbol?
    (list/c 'set type?)
    (cons/c '* (listof type?))
    (cons/c '-> (non-empty-listof type?))
    (list/c tone? type?))))

(define/contract (subtype a b)
  (-> type? type? (or/c #f tone?))
  ;; FIXME!
  (match* (a b)
    ;; functoriality: [T]A <: B  ==> [UT]A <: UB
    [(a `(,(? tone? u) ,b)) (tone* u (subtype a b))]
    ;; adjunction: U -| V and [T]A <: B  ==>  [TU]VA <: B
    [(`(,(? tone? v) ,a) b) (tone* (subtype a b) (tone-left-adjoint v))]
    ;; distribution over products
    [(`(* ,a1 ,a2) `(* ,b1 ,b2))
     (define t (subtype a1 b1))
     (define u (subtype a2 b2))
     (and t u (tone-meet t u))]
    ;; fallthrough, TODO: put at end
    [(_ _) #:when (equal? a b) 'id]
    ;; functions
    [(`(-> ,@as) `(-> ,@bs))
     (error 'subtype "function subtyping unimplemented")]
    [(_ _) #f]))

;; Given a, finds (t, b) such that (t a <: b).
;; Tries to produce a type b without any leading tones.
(define/contract (strip-tones tp)
  (-> type? (values tone? type?))
  (match tp
    [`(,(? tone? v) ,a)
     (define-values (t b) (strip-tones a))
     (values (tone* t (tone-left-adjoint v)) b)]
    [a (values 'id a)]))

(define term?
  (flat-rec-contract term?
   (or/c
    symbol? ;; variables
    number?
    boolean?
    (list/c 'isa type? term?)
    (list/c 'lambda (listof symbol?) term?)
    (non-empty-listof term?) ; fn application
    ;; TODO: let bindings
    ;; TODO: booleans
    ;; TODO: union, intersection, disjunction
    (cons/c 'set (listof term?))
    )))

(define free-vars (make-hash))
(define bound-vars (make-parameter (hash)))
(define/contract (free! x type)
  (-> symbol? type? void?)
  (hash-set! free-vars x type))

(define/contract (elab expected term)
  (-> (or/c type? #f) term? (values type? usage?))

  (define (synth got [usage (hash)])
    (if (not expected) (values got usage)
        (let ([t (subtype got expected)])
         (unless t (error 'elab "got ~s, expected ~s" got expected))
         (values got (usage-scale t usage)))))

  (define (checked-ok usage)
    (unless expected (error "wtf"))
    (values expected usage))

  (match expected
    [`(,(? tone? t) ,a) (checked-ok (usage-scale t (check a term)))]
    [_
     (match term
       [(? symbol?)
        (synth (hash-ref (bound-vars) term
                         (lambda () (hash-ref free-vars term
                                         (lambda () (error "unbound variable" term)))))
               (hash term 'id))]
       [(? number?)  (synth 'num)]
       [(? boolean?) (synth 'bool)]
       [`(isa ,tp ,tm) (synth tp (check tp tm))]
       [`(set ,@elems) (todo)]
       [`(lambda ,vars ,body)
        (match expected
          [`(-> ,@(app reverse (cons b (app reverse as))))
           (unless (= (length as) (length vars))
             (error 'elab "Argument list of wrong length"))
           (parameterize ([bound-vars (apply hash-set* (bound-vars)
                                             (append-map list vars as))])
             (define usage (check b body))
             (for ([var vars])
               (unless (subtone? 'id (hash-ref usage var 'dia))
                 (error 'elab "Non-monotone use of ~s in lambda body ~s" var body))
               (set! usage (hash-remove usage var)))
             (checked-ok usage))]
          [_ (error 'elab "lambda cannot have type: ~s" expected)])]
       ;; TODO: multiargs
       [`(,func ,arg)
        (define-values (ftp fusage) (elab #f func))
        (define-values (t a) (strip-tones ftp))
        (match a
          [`(-> ,b ,c)
           (define argusage (check b arg))
           (synth c (usage-meet (usage-scale t fusage) argusage))]
          [_ (error 'elab "not convertible to function type: ~s" ftp)])]
       )]))

;; (define term?
;;   (flat-rec-contract term?
;;    (or/c
;;     symbol? ;; variables
;;     number?
;;     boolean?
;;     (list/c 'isa type? term?)
;;     (list/c 'lambda (listof symbol?) term?)
;;     (non-empty-listof term?) ; fn application
;;     ;; TODO: let bindings
;;     ;; TODO: booleans
;;     ;; TODO: union, intersection, disjunction
;;     (cons/c 'set (listof term?))
;;     )))

(define/contract (check type x)
  (-> (or/c type? #f) term? usage?)
  (define-values (_ usage) (elab type x))
  usage)

(define (infer x) (elab #f x))
