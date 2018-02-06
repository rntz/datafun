#lang racket

(provide source-info source with-source!)

;; source-info is a parameter for a mutable hash-table (a weak hasheq is
;; suggested, and default) mapping arbitrary things to srclocs.
(define/contract source-info
  (parameter/c (hash/c any/c srcloc? #:immutable #f))
  (make-parameter (make-weak-hasheq)))

;; returns #f if no source info found.
(define (source e)
  (and (source-info) (hash-ref source-info e #f)))

;; returns the object annotated.
(define (with-source! obj loc)
  (when (source-info)
    (hash-set! (source-info) obj loc))
  obj)

;;; Don't need these any more, I think.
;; (require "util.rkt")                    ;assert!
;; (provide source-span-from-port! source-span-from-file source-span-from-string)

;; (define (source-span-from-file source-span filename)
;;   (call-with-input-file* filename (curry source-span-from-port! source-span)))

;; (define (source-span-from-string source-span string)
;;   (source-span-from-port! source-span (open-input-string string)))

;; ;; exclamatory! because it modifies port's position
;; (define (source-span-from-port! source-span port)
;;   ;; (file-position port pos) to set position to pos
;;   (match-define (list (app position-offset start) (app position-offset end))
;;     source-span)
;;   (assert! (< start end))
;;   (file-position port start)
;;   (read-string (- end start) port))
