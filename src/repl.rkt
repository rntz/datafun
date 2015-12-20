#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "env.rkt" "elab.rkt" "compile.rkt")

(define (show-err e) (printf "** ~a\n" (exn-message e)))

(define (repl)
  (let/ec quit
    (printf "- DF> ")
    ;; we do this to prune *elab-info* of unnecessary entries
    (collect-garbage)
    (match (read)
      [(? eof-object?) (quit)]
      [line
       (with-handlers ([exn:fail? show-err])
         (define expr (parse-expr line '()))
         (printf "expr: ~v\n" expr)
         (define expr-type (elab-infer expr empty-env))
         (printf "type: ~v\n" expr-type)
         ;; (display "info: ") (pretty-print *elab-info*)
         (define code (compile-expr expr))
         (display "code: ") (pretty-print (syntax->datum code))
         (printf " val: ~v\n" (eval code)))])
    (repl)))
