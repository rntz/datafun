#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "compile.rkt")

(define (show-err e) (printf "** ~a\n" (exn-message e)))

(struct global (type value) #:transparent)

(define (repl [env (hash)])
  (let/ec quit
    ;; env maps names to globals.
    (define env (hash))
    (define decl-parser empty-decl-state)

    (define (elab-env)
      (env-free-extend empty-env
       (for/hash ([(name g) env])
         (values name (global-type g)))))
    (define (compile-env)
      (env-free-extend empty-env
       (for/hash ([(name g) env])
         ;; this is a terrible hack that only works because racket is amazing
         (values name #`'#,(global-value g)))))

    (define (handle-expr expr)
      (printf "expr: ~v\n" expr)
      (define expr-type (elab-infer expr (elab-env)))
      (printf "type: ~v\n" expr-type)
      (define code (compile-expr expr (compile-env)))
      (display "code: ") (pretty-print (syntax->datum code))
      (printf " val: ~v\n" (eval code)))

    (define (handle-defns defns)
      (for ([d defns] #:when (equal? 'mono (defn-tone d)))
        (error "monotone definitions not allowed at top-level: " d))
      ;; run the defns in order.
      (for ([d defns])
        (match-define (defn name _ type expr) d)
        (printf "defn: ~a = ~a\n" name expr)
        ;; elaborate the expression.
        (match type
          ;; if not type-annotated, try to infer.
          [#f (set! type (elab-infer expr (elab-env)))]
          [_ (elab-check expr type (elab-env))])
        (printf "type: ~v\n" type)
        ;; compile it.
        (define code (compile-expr expr (compile-env)))
        (display "code: ") (pretty-print (syntax->datum code))
        (define val (eval code))
        (printf "val: ~v\n" val)
        ;; bind name to val in env and compile-env
        (set! env (hash-set env name (global type val)))))

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
