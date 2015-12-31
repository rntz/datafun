#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "compile.rkt")

(define (show-err e) (printf "** ~a\n" (exn-message e)))

(define df-debug (make-parameter #t))
(define-syntax-rule (debug body ...) (when (df-debug) body ...))

;; global environments
(struct global (type value) #:transparent)
(define global-env? (hash/c ident? global? #:immutable #t))

(define (elab-env env)
  (make-free-env (hash-map-values global-type env)))

(define (compile-env env)
  (make-free-env
   ;; this is a terrible hack that only works because racket is amazing
   (hash-map-values (lambda (x) #`'#,(global-value x)) env)))


;; Utilities for evaluating things inside a given global-env
(define (eval-file filename env)
  (eval-decls (read-file filename) env))

(define (eval-decls lines env)
  (eval-defns (parse-all-decls lines '()) env))

(define (eval-defns defns env)
  (for ([d defns] #:when (equal? 'mono (defn-tone d)))
    (error "monotone definitions not allowed at top-level: " d))
  ;; run the defns in order.
  (for ([d defns])
    (set! env (eval-defn d env)))
  env)

;; evaluates a definition & updates the global environment.
(define (eval-defn d env)
  (match-define (defn name tone type expr) d)
  (assert! (not (equal? 'mono tone)))
  (debug (printf "defn: ~a = ~a\n" name expr))
  ;; elaborate the expression.
  (match type
    ;; if not type-annotated, try to infer.
    [#f (set! type (elab-infer expr (elab-env env)))]
    [_ (elab-check expr type (elab-env env))])
  (debug (printf "type: ~v\n" type))
  ;; compile it.
  (define code (compile-expr expr (compile-env env)))
  (debug (display "code: ") (pretty-print (syntax->datum code)))
  (define val (eval code))
  (debug (printf "val:  ~v\n" val))
  ;; bind name to val in env and return it.
  (hash-set env name (global type val)))


;; the repl
(define (repl [env (hash)])
  (let/ec quit
    ;; env is a global-env?; it maps names to globals.
    (define decl-parser empty-decl-state)

    (define (handle-expr expr)
      (debug (printf "expr: ~v\n" expr))
      (define expr-type (elab-infer expr (elab-env env)))
      (debug (printf "type: ~v\n" expr-type))
      (define code (compile-expr expr (compile-env env)))
      (debug (display "code: ") (pretty-print (syntax->datum code)))
      (printf "~v\n" (eval code)))

    (define (handle-defns defns)
      (set! env (eval-defns defns env)))

    (define (handle-line line)
      (define (on-err e1 e2)
        (error (format "could not parse declaration: ~a
could not parse expression: ~a" (exn-message e1) (exn-message e2))))
      ((with-handlers ([exn:fail?
                        (lambda (e1)
                          (define expr
                            (with-handlers ([exn:fail? (curry on-err e1)])
                              (parse-expr line '())))
                          (lambda () (handle-expr expr)))])
         (define-values (new-state defns) (parse-decl decl-parser line '()))
         (set! decl-parser new-state)
         (lambda () (handle-defns defns)))))

    ;; main loop
    (let loop ()
      (printf "- DF> ")
      (with-handlers ([exn:fail? show-err])
        (match (read)
          [(? eof-object?) (quit)]
          [line (handle-line line)]))
     (loop))))
