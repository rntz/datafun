#lang racket

(require "util.rkt" "ast.rkt" "parse.rkt" "elab.rkt")

(define (repl)
  (printf "DF- ")
  (define line (read))
  (unless (eof-object? line)
    (with-handlers ([exn:fail? (lambda (e) (printf "** ~a\n" (exn-message e)))])
      (define expr-in (parse-expr line '()))
      (printf "parsed: ~v\n" expr-in)
      (define-values (expr-type expr-elab) (elab-infer '() expr-in))
      (printf "elab: ~v\n" expr-elab)
      (printf "type: ~v\n" expr-type))
    (repl)))
