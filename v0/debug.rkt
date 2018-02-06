#lang racket

(provide (all-defined-out))

(define debug-idents (make-parameter (set)))
(define-syntax-rule (debug ident body ...)
  (when (set-member? (debug-idents) 'ident)
    body ...))

(define-syntax-rule (debugging (ident ...) body ...)
  (parameterize ([debug-idents (set-union (debug-idents) (set 'ident ...))])
    body ...))

(define-syntax-rule (debug! ident ...)
  (debug-idents (set-union (debug-idents) (set 'ident ...))))

(define-syntax-rule (undebug! ident ...)
  (debug-idents (set-subtract (debug-idents) (set 'ident ...))))
