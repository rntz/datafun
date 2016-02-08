#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; our "runtime", of sorts.
(define (df-union . xs) (sets-union xs))
;; side-effecting funs return the empty tuple, '()
(define (df-puts x) (displayln x) '())
(define (df-print x) (println x) '())
(define ((df= x) y) (equal? x y))
(define ((df+ x) y) (+ x y))
(define ((df- x) y) (max 0 (- x y)))
(define ((df* x) y) (* x y))
(define ((df++ x) y) (string-append x y))
(define (df-max . xs) (if (null? xs) 0 (apply max xs)))
(define (df-or . xs) (ormap identity xs))
(define (df-fix init iter)
  (define next (iter init))
  (if (equal? init next) init
      (df-fix next iter)))
(define ((df-lookup d) k)
  (if (hash-has-key? d k)
      (list 'just (hash-ref d k))
      (list 'none)))

;; dynamic diiiiiiiispaaaaaaaaatch b/c why not
(define/match (df<= a)
  [(#f) (const #t)]
  [(#t) (curry equal? #t)]
  [((? number? a)) (curry <= a)]
  [((? string? a)) (curry string<=? a)]
  [((? set? a)) (curry subset? a)]
  ;; sum types needs to come before tuples b/c their representations overlap
  ;; somewhat. NB. would need to change if we had a type whose values were
  ;; symbols.
  [((list (? symbol? tag1) value1))
   (match-lambda [(list (? symbol? tag2) value2)
             (and (equal? tag1 tag2) (df<= value1 value2))])]
  [((? list? as)) (curry andmap (lambda (a b) ((df<= a) b)) as)]
  ;; NB: Both records and maps are represented as hashes. Luckily, the same code
  ;; works for both! (although hash-has-key? is redundant for records)
  [((? hash? a))
   (lambda (b) (for/and ([(k v) a])
            (and (hash-has-key? b k)
                 ((df<= v) (hash-ref b k)))))])

;; this needs us to give it the type, for two reasons:
;; 1. in case `args' is empty.
;; 2. for lub-ing hashes, which represent both Datafun records and maps.
(define (df-lub type args)
  (match type
    [(t-base 'bool) (ormap identity args)]
    [(t-base 'nat) (apply df-max args)]
    [(t-fun _ a b) (lambda (x) (df-lub b (for/list ([f args]) (f x))))]
    [(t-set _) (apply df-union args)]
    [(t-map _ value-type)
     (for/fold ([h (hash)]) ([a args])
       (hash-union-with h a (lambda l (df-lub value-type l))))]
    [(t-tuple ts)
     (for/list ([i (length ts)] [t ts])
       (df-lub t (map (lambda (x) (list-ref x i)) args)))]
    [(t-record fields)
     (for/hash ([(name type) fields])
       (define (get-field x) (hash-ref x name))
       (values name (df-lub type (map get-field args))))]))
