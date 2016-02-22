#lang racket

(provide source-info source-span? get-source-info with-source-info!
         source-span-from-port! source-span-from-file source-span-from-string)

(require parser-tools/lex)            ;for (struct position)

;; A source span is just a pair of positions.
(define source-span? (list/c position? position?))

;; source-info is a parameter for a mutable hash-table (a weak hasheq is
;; suggested, and default) mapping arbitrary things to source spans.
(define/contract source-info
  (parameter/c (hash/c any/c source-span? #:immutable #f))
  (make-parameter (make-weak-hasheq)))

;; returns #f if no source info found.
(define (get-source-info e)
  (and (source-info) (hash-ref source-info e #f)))

;; returns the object annotated.
(define (with-source-info! obj start-pos end-pos)
  (when (source-info)
    (hash-set! (source-info) obj (list start-pos end-pos)))
  obj)

(define (source-span-from-file source-span filename)
  (call-with-input-file* filename (curry source-span-from-port! source-span)))

(define (source-span-from-string source-span string)
  (source-span-from-port! source-span (open-input-string string)))

;; exclamatory! because it modifies port's position
(define (source-span-from-port! source-span port)
  ;; (file-position port pos) to set position to pos
  (match-define (list (app position-offset start) (app position-offset end))
    source-span)
  (assert! (< start end))
  (file-position port start)
  (read-string (- end start) port))
