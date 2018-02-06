#lang racket

(require "util.rkt" "ast.rkt" "source-info.rkt")

(provide (except-out (all-defined-out) tone-sigs type-sigs set-type! set-tone!))

;; Defns are the things the backend cares about. A defn is a self-contained type
;; or value binding.
(enum defn
  ;; type definition
  (d-type name type)
  ;; value definition
  ;; tone is either 'disc, 'mono, or 'anti
  ;; type is #f if no type signature provided.
  (d-val name tone type expr))

;; Decls are the things we let the programmer write. They can specify only a
;; value's type or tone, for example, with the value itself to be defined later.
;; We need to collate decls to produce defns.
(enum decl
  (decl-type name type)
  (decl-val-tone name tone)
  (decl-val-type name type)
  (decl-val name expr))

;; We expose some of the details of this collating process, so that decls can be
;; entered interactively at the repl and collated into defns on-the-fly. This
;; interface is imperfect, but it works.
(define-syntax-rule (with-defn-parser body ...)
  (parameterize ([tone-sigs (make-hash)]
                 [type-sigs (make-hash)])
    body ...))

(define tone-sigs (make-parameter #f))
(define type-sigs (make-parameter #f))
(define (set-type! name type) (hash-set! (type-sigs) name type))
(define (set-tone! name tone) (when tone (hash-set! (tone-sigs) name tone)))

(define (decls->defns ds #:default-tone default-tone)
  (with-defn-parser
    (begin0 (generate/list (parse-defns! ds #:default-tone default-tone))
      (defn-parsing-done!))))

;; TODO: report source info on error
(define (defn-parsing-done!)
  ;; check that we don't have any left over unfulfilled type or tonicity
  ;; ascriptions for variables we haven't defined.
  (for ([(n _) (type-sigs)])
    (error "type signature for undefined variable:" n))
  (for ([(n _) (tone-sigs)])
    (error "tone signature for undefined variable:" n)))

;; generates (as in in-generator/yield) defns.
(define (parse-defns! ds #:default-tone default-tone)
  (for ([d ds]) (parse-defn! d #:default-tone default-tone)))

;; TODO: add source information for definitions
;; TODO: error if overwriting a previous tone or type decl.
(define (parse-defn! d #:default-tone default-tone)
  (match d
    [(decl-type n t)        (yield (d-type n t))]
    [(decl-val-tone n o)    (set-tone! n o)]
    [(decl-val-type n t)    (set-type! n t)]
    [(decl-val name expr)
     (define tone (hash-ref (tone-sigs) name default-tone))
     (define type (hash-ref (type-sigs) name #f))
     (hash-remove! (tone-sigs) name)
     (hash-remove! (type-sigs) name)
     (yield (d-val name tone type expr))]))
