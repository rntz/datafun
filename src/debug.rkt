#lang racket

(provide (all-defined-out))

(define df-debug (make-parameter #f))
(define-syntax-rule (debug body ...) (when (df-debug) body ...))
