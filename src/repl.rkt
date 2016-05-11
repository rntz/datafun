#lang racket

(provide (all-defined-out))

(require "util.rkt" "debug.rkt" "ast.rkt" "types.rkt" "env.rkt" "elab.rkt"
         "defns.rkt" "parser.rkt" "runtime.rkt" "compile.rkt" "to-sexp.rkt")

(define (show-err e)
  (displayln "* ERROR")
  ((error-display-handler) (exn-message e) e))

;; global envs map top-level variables to globals. (and also types to their
;; definitions.)
(struct global (type value) #:transparent)
(define/contract global-env (parameter/c env?) (make-parameter empty-env))

(define (global-elab-env [globals (global-env)])
  (env-map-vars (lambda (g) (hyp 'disc (global-type g))) globals))

(define (global-compile-env [globals (global-env)])
  ;; this is a terrible hack that only works because racket is amazing
  ;; TODO?: map globals to gensyms instead so we can get rid of this awful hack?
  (env-map-vars (lambda (x) #`'#,(global-value x)) globals))


;; the repl
(define (repl)
  (let/ec quit
    (with-defn-parser
      (let loop ()
        (display "- DF> ")
        ;; PROBLEM: can't deal with source info properly since a single defn can
        ;; be formed from multiple different lines collated together! :(
        (define line (read-line))
        (with-handlers ([exn:fail? show-err])
          (do-line line quit))
        (loop)))))

(define (do-line line quit)
  (match line
    [(or (? eof-object?) (app string-trim ":quit")) (quit)]
    [(pregexp #px"^:load\\s*(\\S+)\\s*$" (list _ filename))
     (eval-file! filename)]
    [(app string-trim ":env")
     (match-define (env vars types) (global-env))
     (for ([(name type) types])
       (printf "type ~a = ~s\n" name (type->sexp type)))
     (for ([(name g) vars])
       (match-define (global type value) g)
       (printf "~a : ~s = ~v\n" name (type->sexp type) value))]
    [_ (eval-decl-or-expr line)]))

;; would like a better name. tries multiple things in order, returning the value
;; of the first one that doesn't throw a given error. if all error, calls
;; the given handler with all errors.
(define-syntax with-handlers-each
  (syntax-rules ()
    ((_ ([exn-test? proc] ...) expr)
     (with-handlers ([exn-test? proc] ...) expr))
    ((_ ([exn-test? proc]) expr exprs ...)
     (with-handlers
       ([exn-test?
         (lambda (e) (with-handlers-each ([exn-test? (curry proc e)])
                  exprs ...))])
       expr))))

;;; FIXME TODO: use (parse #:as 'decls-or-expr)!
(define (eval-decl-or-expr line)
  (define (on-err e1 e2)
    (error (format "could not parse declaration: ~a
could not parse expression: ~a" (exn-message e1) (exn-message e2))))
  ((with-handlers-each ([exn:fail? on-err])
     (let ([x (generate/list (parse-defns! (parse-string line #:as 'decls)
                                           #:default-tone 'disc))])
       (lambda () (eval-defns! x)))
     (let ([x (parse-string line #:as 'expr)])
       (lambda () (eval-expr x))))))

(define (eval-file! filename)
  (eval-defns! (decls->defns (parse-file filename #:as 'decls)
                             #:default-tone 'disc)))

;; performs a list of defns within a given environment.
;; for d-types, just binds the type name.
;; for d-vals, evaluates the code & binds the name.
(define (eval-defns! defns)
  ;; we check ALL defns before evaluating ANY of them
  (for ([d defns] #:when (match? d (d-val _ (not 'disc) _ _)))
    (error "monotone/antitone definitions not allowed at top-level: " d))
  (for ([d defns])
    (eval-defn! d)))

;; evaluates a defn in global-env.
(define/match (eval-defn! d)
  [((d-type name type))
   (global-env (env-bind-type name type (global-env)))]
  [((d-val name 'disc decl-type expr))
   (debug eval (printf "defn: ~a = ~s\n" name (expr->sexp expr)))
   ;; elaborate the expression.
   (define-values (elab-info type)
     (elab expr #:type decl-type #:env (global-elab-env)))
   (debug eval (printf "type: ~s\n" (type->sexp type)))
   ;; compile it.
   (define code (compile expr #:info elab-info #:env (global-compile-env)))
   (debug eval (display "code: ") (pretty-print (syntax->datum code)))
   (define val (eval code))
   (debug eval (printf "val:  ~v\n" val))
   ;; bind name to val in global-env.
   (global-env (env-bind-var name (global type val) (global-env)))])

(define (eval-expr expr)
  (debug eval (printf "expr: ~s\n" (expr->sexp expr)))
  (define-values (elab-info expr-type)
    (elab expr #:env (global-elab-env)))
  (debug eval (printf "type: ~s\n" (type->sexp expr-type)))
  (define code
    (compile expr #:info elab-info #:env (global-compile-env)))
  (debug eval (display "code: ") (pretty-print (syntax->datum code)))
  (define value-string (pretty-format (eval code)))
  ;; print type annotation on next line if value takes multiple lines
  (printf (if (string-contains? value-string "\n") "~a\n: ~s\n" "~a : ~s\n")
          value-string (type->sexp expr-type)))
