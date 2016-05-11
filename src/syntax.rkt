#lang racket

(provide (all-defined-out))

(require syntax/parse)
(require "util.rkt")

(enum datafun-form
  ;; expand : syntax -> syntax
  (datafun-macro expand)
  ;; infer   : ??
  ;; compile : ??
  (datafun-prim  infer compile))

(define (datafun-expand stx)
  (syntax-parse stx
    [(form:id arg ...)
     (match-define (list _ ) (identifier-binding form)
       )]))
