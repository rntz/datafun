#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; a context is a list of entries. an entry has a type & a usage. usages are
;; 'any for unrestricted variables, 'mono for monotone variables, or 'hidden for
;; once-monotone variables hidden by a shift to constant context.
(struct entry (type usage) #:transparent)
(define usage? (or/c 'any 'mono 'hidden))

(define env-cons cons)
(define env-ref list-ref)
(define (env-extend extension env) (append (reverse extension) env))

;; Elaborated expression forms:
;; e-app-{fun,mono} distinguish applying functions from monotone functions
(struct e-app-fun e-app () #:transparent)
(struct e-app-mono e-app () #:transparent)

(define (type-error fmt . args)
  (error (apply format (string-append "type error: " fmt) args)))

;; returns two values: type & elaborated expression.
(define (elab-synth Γ e)
  (match e
    [(e-ann e t) (elab-check Γ t e)]
    [(e-var _ i) (env-ref Γ i)]
    [(e-lit v) (lit-type v)]
    [(e-prim p)
      (define t (prim-infer-type p))
      (if t t (type-error "can't infer type of primitive ~a" p))]
    [(e-fun )]
    ))

;; returns elaborated expression.
(define (elab-check Γ t e)
  (match e
    ))
