#lang racket

;;; ========== Module with identifiers for representing Datafun ==========
(define-syntax-rule (declare id ...)
  (begin
    (provide id ...)
    (define-syntax id #f) ...))

;; (require syntax/parse)
;; (define-syntax-rule (define-class class? id ...)
;;   (begin
;;     (define (class? e)
;;       (syntax-parse e
;;         [(id _ (... ...)) #t] ...))))
;; (define-class decl? define-type value-has-type define-value)


;; tones
(declare any mono anti)

;; declaration forms
(declare define-type value-has-type define-value)

;; type forms
(declare Name Sum Tuple Record Fun Set Map)

;; pattern forms (that aren't also expression forms)
(declare
 ;; wild
 ;; (and pat ...)
 ;; (or pat ...)
 ;; (eq expr)
 wild and or eq
 ;; -- others (that are also expressions):
 ;; (var name)
 ;; (lit literal)
 ;; (tuple pat ...)
 ;; (tag name pat ...)
 )


;; expressions
(declare
 ;; ---------- misc ----------
 ;; (isa type expr)
 ;; (lit literal)
 ;; (prim name)
 ;; (var name)
 ;; (trustme expr), moves all mono/antitone variables into unrestricted context
 isa lit prim var trustme

 ;; ---------- binding ----------
 ;; (let tone name expr expr)
 ;; (let-type name type expr)
 let let-type

 ;; ---------- functions ----------
 ;; (fn name expr)
 ;; (call expr expr)
 fn call

 ;; ---------- booleans ----------
 ;; (if expr expr expr)
 if

 ;; -- Notes on typechecking `if':
 ;; (if e1 empty empty) checks e1 with all vars unrestricted (a la `trustme')
 ;; (if e1 e2 empty)    is monotone in e1
 ;; (if e1 empty e2)    is antitone in e1
 ;; (if e1 e2 e3)       otherwise requires e1 to be constant

 ;; ---------- tuples & records ----------
 ;; (tuple expr ...)
 ;; (record [name expr] ...)
 ;; (proj index expr) where index is either a number or a symbol
 ;; (record-merge expr expr)
 ;; TODO?: (record-project expr name ...) project a set of fields
 tuple record proj record-merge

 ;; ---------- sums & pattern matching ----------
 ;; (tag name expr ...)
 ;; (case expr [pat expr] ...)
 tag case

 ;; ---------- sets ----------
 ;; (make-set expr ...)
 ;; (set-bind pat expr expr)
 make-set set-bind

 ;; ---------- maps ----------
 ;; (make-map [expr expr] ...)
 ;; (tabulate x:var e1:expr e2:expr) = {x: e2 | x in e1}
 ;; (map-get map:expr key:expr)
 ;; (map-bind k:pat v:var e1:expr e2:expr) = lub {e2 | (k,v) in e1}
 make-map tabulate map-get map-bind

 ;; TODO: Neel pointed out some cleaner primitive most of these can be written
 ;; in terms of - check notebook.

 ;; ---------- semilattices ----------
 ;; (lub expr ...); empty is (lub)
 ;; (fix var expr)
 lub fix)
