#lang racket

(require "util.rkt" "ast.rkt" "types.rkt" "parse.rkt" "env.rkt" "elab.rkt"
         "compile.rkt")
(provide (all-defined-out))

(define (show-err e) (printf "** ~a\n" (exn-message e)))

(define df-debug (make-parameter #f))
(define-syntax-rule (debug body ...) (when (df-debug) body ...))

;; global environments
(struct global (type value) #:transparent)
(define global-env? (hash/c ident? global? #:immutable #t))

(define (global-elab-env env)
  (hash->env (hash-map-values (lambda (g) (hyp 'any (global-type g))) env)))

(define (global-compile-env env)
   ;; this is a terrible hack that only works because racket is amazing
  (hash->env (hash-map-values (lambda (x) #`'#,(global-value x)) env)))


;; Utilities for evaluating things inside a given global-env
(define (eval-file filename env)
  (eval-decls (read-file filename) env))

(define (eval-decls lines env)
  (eval-defns (parse-all-decls lines) env))

(define (eval-defns defns env)
  (for ([d defns] #:when (equal? 'mono (defn-tone d)))
    (error "monotone definitions not allowed at top-level: " d))
  (for ([d defns])
    (set! env (eval-defn d env)))
  env)

;; evaluates a definition in a global-env. returns updated env.
(define (eval-defn d env)
  (match-define (defn name tone decl-type expr) d)
  (assert! (not (equal? 'mono tone)))
  (debug (printf "defn: ~a = ~s\n" name (expr->sexp expr)))
  ;; elaborate the expression.
  (define-values (elab-info type)
    (elab expr #:type decl-type #:env (global-elab-env env)))
  (debug (printf "type: ~s\n" (type->sexp type)))
  ;; compile it.
  (define code (compile-expr expr (global-compile-env env) elab-info))
  (debug (display "code: ") (pretty-print (syntax->datum code)))
  (define val (eval code))
  (debug (printf "val:  ~s\n" val))
  ;; bind name to val in env and return it.
  (hash-set env name (global type val)))


;; the repl
(define *repl-env* (box (hash)))

(define (repl [env-box *repl-env*])
  ;; env-box is a box containing a global-env mapping names to globals.
  (define (env) (unbox env-box))
  (define (set-env! e) (set-box! env-box e))

  ;; what we use to parse decls. gets set! repeatedly in the main loop.
  (define decl-parser empty-decl-state)

  (define (handle-expr expr)
    (debug (printf "expr: ~s\n" (expr->sexp expr)))
    (define-values (elab-info expr-type)
      (elab expr #:env (global-elab-env (env))))
    (debug (printf "type: ~s\n" (type->sexp expr-type)))
    (define code (compile-expr expr (global-compile-env (env)) elab-info))
    (debug (display "code: ") (pretty-print (syntax->datum code)))
    (define value-string (pretty-format (eval code)))
    ;; print type annotation on next line if value takes multiple lines
    (printf (if (string-contains? value-string "\n") "~a\n: ~s\n" "~a : ~s\n")
            value-string (type->sexp expr-type)))

  (define (handle-defns defns)
    (set-env! (eval-defns defns (env))))

  (define (handle-line line)
    (define (on-err e1 e2)
      (error (format "could not parse declaration: ~a
could not parse expression: ~a" (exn-message e1) (exn-message e2))))
    ((with-handlers ([exn:fail?
                      (lambda (e1)
                        (define expr
                          (with-handlers ([exn:fail? (curry on-err e1)])
                            (parse-expr line)))
                        (lambda () (handle-expr expr)))])
       (define-values (new-state defns) (parse-decl decl-parser line))
       (set! decl-parser new-state)
       (lambda () (handle-defns defns)))))

  ;; main loop
  (let/ec quit
    (let loop ()
      (display "- DF> ")
      (with-handlers ([exn:fail? show-err])
        (match (read)
          [(or #:quit (? eof-object?)) (quit)]
          [#:debug (df-debug (not (df-debug)))]
          [`(#:load ,filename)
           (unless (string? filename) (error "filename must be a string"))
           (set-env! (eval-file filename (env)))]
          [#:env (for ([(name g) (env)])
                   (match-define (global type value) g)
                   (printf "~a : ~s = ~v\n" name (type->sexp type) value))]
          [line (handle-line line)]))
      (loop))))
