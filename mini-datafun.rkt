#lang racket

;; A "mini-Datafun" implemented as a collection of Racket functions and macros,
;; with a collection of commented examples. Hopefully a nice introduction to the
;; core computational ideas of Datafun if you already know Racket or Scheme.
;;
;; mini-Datafun HAS:
;; - fixed points
;; - set comprehensions
;;
;; mini-Datafun LACKS:
;; - any optimizations whatsoever
;; - type checking
;; - monotonicity
;; - termination checking
;; - semilattice/fixed-point types other than sets
;; - incrementalization / seminaive evaluation
;;
;; For more on those, see:
;; - Datafun's website      http://www.rntz.net/datafun/
;; - The ICFP 2016 paper    http://www.rntz.net/files/datafun.pdf
;; - Our github repo        https://github.com/rntz/datafun/
;;
;; September 2017, Michael Arntzenius, daekharel at gmail dot com

(provide empty union fixed-point fix let*/set join setof)
(require syntax/parse/define)

 ;; ---------- Basic functions ----------
;; A finite set data structure is included in Racket's standard library. Racket
;; makes sets as easy to work with as lists; the 'set function constructs sets,
;; just like 'list constructs lists. (set 1 2 3) == (set 3 2 1) == (set 1 3 1 2)
;; all construct the set containing 1, 2, and 3.
(define empty (set))
(define (union . xs) (apply set-union (set) xs))

 ;; ---------- Fixed points ----------
;; Given a function `f` and an initial value `init` (by default, the empty set),
;; repeatedly applies `f` until it reaches a value `x` such that
;; `(equal? x (f x))`, i.e. a fixed point of `f`.
;;
;; Of course, we may never find such an `x`. In Datafun proper, the type system
;; restricts uses of `fixed-point` in a way that ensures we always do.
(define (fixed-point f #:init [init (set)])
  (define next (f init))
  (if (equal? init next) init
      (fixed-point f #:init next)))

;; (fix x some-expr) == (fixed-point (lambda (x) some-expr))
(define-simple-macro (fix x:id M:expr)
  (fixed-point (lambda (x) M)))

;; (let*/set ([x indices]) inner-set) computes the union of all `inner-set`s
;; for each x in `indices`. It's the monadic bind operator for sets.
(define-simple-macro (let*/set (for-clause ...) body ...+)
  (for*/set (for-clause ... [result (begin body ...)]) result))

 ;; ---------- Set comprehensions ----------
;; Most of this is Racket macro magic which you can ignore. I think the best way
;; to understand it is via the examples below.
(begin-for-syntax
 (define-syntax-class definition
   #:literals (define)
   (pattern (define stuff ...))))

;; (join L ... M) is Datafun's (⋁(L ...) M), more or less.
(define-syntax-parser join
  #:datum-literals (<-) #:literals (when)
  ;; base case
  [(join body:expr) #'body]
  ;; mixing definitions into your comprehensions can be handy
  [(join d:definition ...+ body ...+) #'(local (d ...) (join body ...))]
  ;; a small optimization that gives nicer-looking macroexpansions
  [(join (x:id <- M:expr) ...+ L ...+) #'(let*/set ([x M] ...) (join L ...))]
  ;; comprehending/looping across a set
  [(join (p <- M:expr) L ...+)
   #'(let*/set ([tmp M])
       (match tmp [p (join L ...)] [_ (set)]))]
  ;; conditioning/filtering
  [(join (when condition:expr) L ...+)
   #'(if condition (join L ...) (set))])

;; (setof M L ...) is a traditional set comprehension: {M | L ... }
(define-simple-macro (setof M:expr L ...) (join L ... (set M)))

 ;; ---------- Examples ----------
;; Many of these examples are taken from the Datafun ICFP 2016 paper,
;; http://www.rntz.net/files/datafun.pdf

;; Mapping a function across a set, {f x | x ∈ S}.
(define (smap f S)
  (setof (f x) (x <- S)))

;; Filtering a set, {x | x ∈ S, f x}
(define (sfilter p S)
  (setof x
    (x <- S)
    (when (p x))))

;; Cross product of two sets.
(define (cross A B)
  (setof (list a b)
     (a <- A)
     (b <- B)))

;; Unfortunately we cannot define a membership test since mini-Datafun does not
;; support booleans as a semilattice type. Use Racket's (set-member? set elem)
;; function instead.

;; Intersection of two sets.
(define (intersect A B)
  (setof x
    (x <- A)
    (y <- B)
    (when (equal? x y))))

;; An equivalent, shorter definition using equality-test patterns.
;; Below, (== x) is a pattern that matches only if it receives a value equal to
;; `x`. You can find documentation on pattern-matching in Racket at
;; https://docs.racket-lang.org/reference/match.html
(define (intersect-variant A B)
  (setof x
    (x <- A)
    ((== x) <- B)))

;; The composition of binary relations R and S; relates x to z iff ∃y such that
;; xRy and ySz.
;;
;; I represent binary relations as sets of tuples, and tuples as lists of fixed
;; length. For example, a 2-tuple (x,y) is represented as '(x y).
(define (compo R S)
  (join
    ;; The pattern to match a 2-element list in Racket is (list P Q), where P
    ;; and Q are patterns for its elements.
    ((list x y)      <- R)  ;; for every tuple (x y) in R,
    ((list (== y) z) <- S)  ;; for every tuple (y z) in S, where this y equals that previous y,
    (set (list x z))))      ;; yield the tuple (x z).

;; The quasiquotations here are a feature of Racket's pattern matching system.

 ;; ---------- Example: transitive closure ----------
;; My favorite example program: transitive closure of a relation, or determining
;; reachability (by one or more edges) in a graph.
(define (paths edges)
  ;; A path is either an edge or a composition of two paths.
  (fix self (union edges (compo self self))))

(define diamond-graph (set '(a b) '(a c) '(b d) '(c d)))
(define line-graph (set '(0 1) '(1 2) '(2 3) '(3 4)))

(define (test-paths)
  (printf "diamond-graph: ~v\n" (paths diamond-graph))
  (printf "line-graph: ~v\n" (paths line-graph)))

 ;; ---------- Example: CYK parsing ----------

;; We represent grammars as sets of production rules.
;;
;; A production rule is either:
;; - a 2-tuple (P s),   representing:   P --> s
;; - a 3-tuple (P Q R), representing:   P --> Q R
;;
;; where P, Q, R are symbols standing for nonterminals, and s is a string. This
;; is a variant of Chomsky Normal Form. It's not very convenient to write
;; grammars like this, but every context-free grammar can be put into this form.

;; Here's an example grammar, for well-balanced strings of parentheses.
;; Conceptually, it has three rules:
;;
;;     term --> ""
;;     term --> "(" term ")"
;;     term --> term term
;;
;; To put this in Chomsky normal form, we need a few auxiliary nonterminals.
(define paren-grammar
  (set '(term "")                       ;; term --> ""
       '(term LP rest) '(rest term RP)  ;; term --> "(" term ")"
       '(term term term)                ;; term --> term term
       '(LP "(") '(RP ")")))            ;; nonterminals for parentheses

;; The CYK algorithm can be viewed as a forward-chaining logic program which
;; repeatedly derives "facts" of the form (P i j), where P is a nonterminal, and
;; i and j are indices with i <= j+1. The fact (P i j) means that the substring
;; of the text from i to j inclusive can be produced by the nonterminal P.

;; In (cyk-step text grammar chart),
;;
;; - `text` is the string we are trying to parse;
;; - `grammar` is the grammar (set of rules);
;; - `chart` is a set of derived CYK facts.
(define (cyk-step text grammar chart)
  (union
   ;; try to derive using rules of the form (P Q R)
   ;; by concatenating already-derived facts for Q and R.
   (join ((list P Q R)           <- grammar)
         ((list (== Q) i j)      <- chart)
         ((list (== R) (== j) k) <- chart)
         (set (list P i k)))
   ;; try to derive using rules of the form (P s)
   ;; by matching `s` against every possible position in `text`.
   (join ((list P s) <- grammar)
         (define n (string-length s))
         (i <- (range (+ 1 (- (string-length text) n))))
         ;; (define _ (printf "substring ~v ~v ~v\n" text i n))
         (when (equal? s (substring text i (+ i n))))
         (set (list P i (+ i n))))))

;; To find the chart (set of derived facts) for a given text, we just find the
;; fixed-point of cyk-step.
(define (cyk-run text grammar)
  (fix chart (cyk-step text grammar chart)))

;; Yields the set of nonterminals which can generate the given string.
(define (cyk-parse text grammar)
  (define n (string-length text))
  (define chart (cyk-run text grammar))
  (setof a ((list a 0 (== n)) <- chart)))

;; For example:
(define (balanced-parens? text)
  (set-member? (cyk-parse text paren-grammar) 'term))

;; Of course, parsing balanced parens is quite easy. But the above algorithm
;; should work for *any* CFG (as long as you put it in Chomsky normal form) -
;; even that of a full-fledged programming language.
;;
;; Performance is probably terrible, though. In theory CYK is O(n^3), a
;; respectable-but-slow worst case, but I think that to achieve that bound in
;; Datafun you'd need to index your set of facts carefully, which neither this
;; mini-Datafun nor the fuller-featured Datafun implementation we built for the
;; ICFP 2016 paper can do.
;;
;; Moreover, if I recall correctly, CYK is not just O(n^3) in the worst case but
;; even in the best case. So, whether Datafun is a good language for writing
;; parsers in remains to be seen :).
