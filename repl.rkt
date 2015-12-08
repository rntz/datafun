#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "elab.rkt")

(define (show-err e) (printf "** ~a\n" (exn-message e)))

(define (repl)
  (let/ec quit
    (printf "- DF> ")
    (match (read)
      [(? eof-object?) (quit)]
      [line
       (with-handlers ([exn:fail? show-err])
         (define expr-in (parse-expr line '()))
         (printf "expr: ~v\n" expr-in)
         (define expr-type (elab-infer expr-in '()))
         (printf "type: ~v\n" expr-type)
         (printf "info: ~v\n"
                 (for/hasheq ([(k v) *elab-info*]) (values k v))))])
    (repl)))
