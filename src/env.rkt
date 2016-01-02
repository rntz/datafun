#lang racket

(require "util.rkt")

(provide (all-defined-out))

;; An env is a hash from variable names to info. An env is agnostic about what
;; the info it carries looks like - in a typed language, it would be a
;; parameterized type.
(define env? (hash/c symbol? any/c #:immutable #t))

(define hash->env identity)
(define empty-env (hash))
(define env-ref hash-ref)
(define (env-bind name info env) (hash-set env name info))
(define env-map hash-map-values)
(define (env-extend env ids infos)
  (hash-union-right env (make-immutable-hash (map cons ids infos))))
