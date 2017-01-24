#lang racket

;; idea about errors:
;; can do (with-context exn-pred? some-message ...)
;; and if we get an error satisfying exn-pred?, we prepend "some-message" to it
;; this is used to provide context for error messages, for example:
;;
;;     (with-exn-context (format "while type-checking ~s" some-expr)
;;       ... typecheck some-expr ...)
;;
;; also, we can do: (join-errors exn1 exn2 ... exnk)
;;
;; which joins errors together, saying that we failed because *all* of the
;; following errors occurred. this is useful when an error happens *during* the
;; handling of an error, for example, because we're backtracking-on-error.
;;
;; so error messages have a treelike structure!
;;
;; https://twitter.com/arntzenius/status/693548990604955650
;;
;; errors e ::= message | (context e ... e)
;; context = string
;; message = string

(require "util.rkt")
(provide (all-defined-out))

(struct exn:with-context exn:fail (reasons)
  #:extra-constructor-name make-exn:with-context
  #:transparent)

(define (exn-render e) TODO) ;; produces human-readable error message
(define (wrap-exn ctx e) TODO)
(define (combine-exns a b) TODO)
(define (exn-throw msg) TODO)

(define exn-reasons?
  (listof (or/c string?
                (cons/c string? (recursive-contract exn-reasons? #:flat)))))

(define-syntax (with-exn-context ctx body ...)
  (with-handlers ([exn:with-context? (lambda (e) (raise (wrap-exn ctx e)))])
    body ...))

(define-syntax-parser try-each
  [(e) #'e]
  [(e es ...)
   #'(with-handlers
       ([exn:with-context?
         (lambda (a) (with-handlers
                  ([exn:with-context? (lambda (b) (raise (combine-exns a b)))])
                  (try-each es ...)))])
       e)])
