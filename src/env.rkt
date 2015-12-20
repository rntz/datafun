#lang racket

(require "util.rkt")

(provide (all-defined-out))

;; An env is a list of info for each bound variables (a list suffices b/c we use
;; debruijn indices), and a hash mapping "free" variable names to their info. An
;; env is agnostic about what the info it carries looks like - in a typed
;; language, it would be a parameterized type.
(struct env (free bound) #:transparent
  #:constructor-name make-env)

(define empty-env (make-env (hash) '()))

(define (env-map f e)
  (make-env (hash-map-values f (env-free e)) (map f (env-bound e))))

;; manipulating bound variables
(define (env-ref e i [orelse (lambda () (error "unbound variable"))])
  (with-handlers ([exn:fail:contract? (lambda (_) (orelse))])
    (list-ref (env-bound e) i)))
(define (env-cons info e)
  (make-env (env-free e) (cons info (env-bound e))))
(define (env-extend e infos)
  (make-env (env-free e) (append (reverse infos) (env-bound e))))
(define (env-map-bound f e)
  (make-env (env-free e) (map f (env-bound e))))

;; manipulating free variables
(define (env-free-ref e n [orelse (lambda () (error "no such free variable"))])
  (hash-ref (env-free e) n orelse))
(define (env-free-extend e h)
  (make-env (hash-union-right (env-free e) h) (env-bound e)))
