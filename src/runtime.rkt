#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; our "runtime", of sorts.
(define (df-union . xs) (set-unions xs))
;; side-effecting funs return the empty tuple, '()
(define (df-puts x) (displayln x) '())
(define (df-print x) (println x) '())
(define ((df= x) y) (equal? x y))
(define ((df+ x) y) (+ x y))
(define ((df- x) y) (- x y))
(define ((df* x) y) (* x y))
(define ((df<= x) y) (<= x y))
(define ((df++ x) y) (string-append x y))
(define ((df-subset? x) y) (subset? x y))
(define (df-max . xs) (if (null? xs) 0 (apply max xs)))
(define (df-or . xs) (ormap identity xs))
(define (df-fix init iter)
  (define next (iter init))
  (if (equal? init next) init
      (df-fix next iter)))

;; this needs us to give it the type, in case `args' is empty.
(define (df-join type args)
  (match type
    [(t-bool) (ormap identity args)]
    [(t-nat) (apply df-max args)]
    [(t-set _) (apply df-union args)]
    [(t-fun _ a b) (lambda (x) (df-join b (for/list ([f args]) (f x))))]
    [(t-tuple ts)
     (for/list ([i (length ts)] [t ts])
       (df-join t (map (lambda (x) (list-ref x i)) args)))]
    [(t-record fields)
     (for/hash ([(name type) fields])
       (define (get-field x) (hash-ref x name))
       (values name (df-join type (map get-field args))))]))
