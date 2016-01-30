;; idea about errors:
;; can do (with-context exn-pred? some-message ...)
;; and if we get an error satisfying exn-pred?, we prepend "some-message" to it
;; this is used to provide context for error messages, for example:
;;
;;     (with-context exn:type-check? (format "while checking ~s" some-expr)
;;       ... typecheck some-expr ...)
;;
;; also, we can do: (join-errors exn1 exn2 ... exnk)
;;
;; which joins errors together, saying that we failed because *all* of the
;; following errors occurred. this is useful when an error happens *during* the
;; handling of an error, for example, because we're backtracking-on-error.
;;
;; so error messages have a treelike structure!
;;
;; https://twitter.com/arntzenius/status/693548990604955650
;;
;; errors e ::= message | (context e ... e)
;; context = string
;; message = string
