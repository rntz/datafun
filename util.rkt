#lang racket

(require racket (for-syntax syntax/parse))


;;; Syntax utilities
(provide
  define-syntax-parser TODO fn enum enum-case
  ;; re-export
  (for-syntax syntax-parse syntax-parser))

(define-syntax define-syntax-parser
  (syntax-parser
    [(_ name:id (pattern body ...) ...)
      #'(define-syntax name
          (syntax-parser
            (pattern body ...)
            ...))]
    [(_ (name:id pattern ...) body ...)
      #'(define-syntax-parser name
          [(_ pattern ...) body ...])]))

(define-syntax-parser TODO
  [_:id #'(error "TODO: unimplemented")])

(begin-for-syntax
  (define-syntax-class fn-clause
    (pattern ((param ...) body ...)
      #:attr pattern #'(list param ...))
    (pattern ((param ... . rest-param:id) body ...)
      #:attr pattern #'(list-rest param ... rest-param))))

(define-syntax-parser fn
  [(_ (name params ...) body ...)
    #'(define (name params ...) body ...)]
  [(_ name:id c:fn-clause ...)
    #'(define/match (name . _)
        [(c.pattern) c.body ...]
        ...)])

(define-syntax-rule (enum-case enum-name (branch-name args ...))
  (struct branch-name enum-name (args ...) #:transparent))

(define-syntax-rule (enum name branch ...)
  (begin
    (struct name () #:transparent)
    (enum-case name branch) ...))


;;; Miscellaneous utilities
(provide assert! warn! flip andf orf print-error index-of eqmap foldl1 foldr1)

(define (assert! t) (unless t (error "ASSERTION FAILURE")))
(define (warn! msg) (displayln (format "WARNING: ~a" msg)) )

(define ((flip f) x y) (f y x))         ;do we need this?

(define ((andf . fs) . as) (for/and ([f fs]) (apply f as)))
(define ((orf . fs) . as) (for/or ([f fs]) (apply f as)))

(define (print-error err)
  (printf "error: ~a\n" (exn-message err)))

(define (index-of v lst)
  (let loop ([i 0] [l lst])
    (match l
      ['() #f]
      [(cons x xs) (if (equal? x v) i (loop (+ 1 i) xs))])))

(define (eqmap eq l . lsts)
  (define len (length l))
  (and (andmap (lambda (l) (= len (length l))) lsts)
       (apply andmap eq l lsts)))

(define (foldl1 f l)
  (foldl f (car l) (cdr l)))

(define (foldr1 f l)
  (foldl1 f (reverse l)))


;;; stream utilities
(provide stream-take stream-append-lazy)

(define (stream-take n s)
  (for/list ([x (in-stream s)]
             [_ (in-range n)])
    x))

(define (stream-append-lazy stream stream-thunk)
  (if (stream-empty? stream) (stream-thunk)
    (stream-cons (stream-first stream)
      (stream-append-lazy (stream-rest stream stream-thunk)))))


;;; set utilities
(provide freeze-set set-unions set-intersects set-filter)

(define (freeze-set s) (for/set ([x s]) x))

(define (set-unions sets)
  ;;(let*/set ([s sets]) s)
  (if (null? sets) (set) (apply set-union sets)))

(define (set-intersects sets)
  (apply set-intersect sets))

(define (set-filter p s)
  (for/set ([x s] #:when (p x)) x))


;;; hash utilities
(provide freeze-hash hash-union-with hash-intersection-with
  hash-filter-keys hash-select-keys hash-map-values)

(define (freeze-hash h) (for/hash ([(k v) h]) (values k v)))

(define (hash-filter-keys p h)
  (for/hash ([(k v) h] #:when (p k)) (values k v)))

(define (hash-select-keys h k)
  (hash-filter-keys (curry set-member? (for/set ([x k]) x)) h))

(define (hash-map-values f h)
  (for/hash ([(k v) h])
    (values k (f v))))

(define (hash-union-with a b f)
  (define keys (set-union (list->set (dict-keys a)) (list->set (dict-keys b))))
  (for/hash ([k keys])
    (values k
      (if (not (dict-has-key? a k))
        (dict-ref b k)
        (if (not (dict-has-key? b k))
          (dict-ref a k)
          (f (dict-ref a k) (dict-ref b k)))))))

(define (hash-intersection-with a b f)
  (for/hash ([k (in-dict-keys a)]
              #:when (dict-has-key? b k))
    (f (dict-ref a k) (dict-ref b k))))
