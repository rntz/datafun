#lang racket

(require syntax/parse/define)
(provide TODO length=? let*/list list*/c qq-flat-contract define-flat-contract define-flat-contracts)

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])

(define (length=? x y) (= (length x) (length y)))

(define-syntax-rule (let*/list (for-clause ...) body)
  (for*/list (for-clause ... [x body]) x))

(define (list*/c fst . rest)
  (if (null? rest) fst
      (cons/c fst (apply list*/c rest))))

;; Let's define a quasiquoter that generates contracts.
(define-for-syntax quasiquote-contract
  (syntax-parser
    #:literals (unquote unquote-splicing)
    [(_ name:id) #''name]
    [(_ ,x:expr) #'x]
    [(_ ,@x:expr) (error "uh-oh, that's a weird place to put an unquote-splicing")]
    [(_ (x ... ,@tail)) #'(list*/c (quasiquote/c x) ... tail)]
    [(_ (x ...)) #'(list/c (quasiquote/c x) ...)]))

(define-syntax quasiquote/c quasiquote-contract)

;; Makes quasiquote invoke quasiquote/c.
(define-simple-macro (qq-flat-contract contract-expr)
  #:with quasiquote (datum->syntax #'contract-expr 'quasiquote)
  (let-syntax ([quasiquote quasiquote-contract]) contract-expr))

;; A simple macro for defining flat contracts, where quasiquotation uses
;; quasiquote/c.
(define-syntax-rule (define-flat-contracts [name contract ...] ...)
  (define-values (name ...)
    (flat-murec-contract ([name (qq-flat-contract contract) ...] ...)
     (values name ...))))

(define-syntax-rule (define-flat-contract name contract ...)
  (define-flat-contracts [name contract ...]))
