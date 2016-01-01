#lang racket

(require (except-in syntax/parse expr))
(require "util.rkt" "ast.rkt")

(define (ident? x) (and (symbol? x) (not (reserved? x))))
(define (reserved? x) (set-member? reserved x))
(define reserved
  (list->set '(: = mono <- -> ~>
               empty fn λ cons π proj record record-merge extend-record tag
               quote case if join set let where fix)))

(define-syntax-class ident
  (pattern name:id #:when (ident? (syntax->datum #'name))))

(define parse-expr
  (syntax-parser
    [name:ident ]
    ))

