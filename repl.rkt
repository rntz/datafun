#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "elab.rkt")

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
         (define expr-in (parse-expr line '()))
         (printf "expr: ~v\n" expr-in)
         (define expr-type (elab-infer expr-in '()))
         (printf "type: ~v\n" expr-type)
         (display "info: ") (pretty-print *elab-info*))])
    (repl)))
