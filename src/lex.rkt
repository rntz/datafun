#lang racket

(provide (all-defined-out))

(require parser-tools/lex)
(require (prefix-in : parser-tools/lex-sre))

;; ========== TOKENS ==========
(define-tokens datafun-tokens (number string id Id))
(define-empty-tokens datafun-empty-tokens
  (eof
   ;; punctuation
   LP RP LSQUARE RSQUARE LCURLY RCURLY
   DOT BANG QUERY COMMA : SEMI _ BAR & BARBAR &&
   = <= < >= >
   -> ~> ->- ->+ =>
   + * - / ++ **
   ∨ ∈ ⋁ • ×
   ;; declarations
   TYPE VAL FUN REL DISC MONO ANTI
   ;; types
   SET MAP
   ;; expressions
   LAMBDA LET CASE IF THEN ELSE WHEN UNLESS FIX IS
   IN IN? FOR LUB
   TRUE FALSE EMPTY))


;; ========== LEXER ==========
(define datafun-lex
  (lexer-src-pos
   ;; whitespace & comments
   [(:+ whitespace) (return-without-pos (datafun-lex input-port))]
   ;; we don't support nested comments yet, alas.
   [(:: "(*" (complement (:: any-string "*)" any-string)) "*)")
     (return-without-pos (datafun-lex input-port))]

   ;; literals
   [(:+ numeric) (token-number (string->number lexeme))]
   [(:: "\"" (:* (:or (:~ "\"") (:: "\\" any-char))) "\"")
    (token-string (with-input-from-string lexeme read))]

   ;; punctuation and symbols
   ["(" 'LP]      [")" 'RP]
   ["{" 'LCURLY]  ["}" 'RCURLY]
   ["[" 'LSQUARE] ["]" 'RSQUARE]
   ["." 'DOT] ["!" 'BANG] ["?" 'QUERY]
   ["," 'COMMA] [":" ':] [";" 'SEMI] ["_" '_]
   ["|" 'BAR] ["&" '&] ["||" 'BARBAR] ["&&" '&&]
   ["=" '=] ["<=" '<=] ["<" '<] [">=" '>=] [">" '>]
   ["=>" '=>] ["->" '->] ["~>"  '~>] ["->+" '->+] ["->-" '->-]
   ["→" '->] ["→⁺" '->+] ["→⁻" '->-]
   ["+" '+] ["-" '-] ["*" '*] ["/" '/] ["++" '++] ["**" '**]
   ["∨" '∨] ["⋁" '⋁] ["∈" '∈] ["•" '•] ["×" '×]

   ;; declaration keywords
   ["type" 'TYPE]   ["val" 'VAL]   ["fun" 'FUN]     ["rel" 'REL]
   ["disc" 'DISC]   ["mono" 'MONO] ["anti" 'ANTI]

   ;; type keywords
   ;; ["set" 'SET] ["map" 'MAP]

   ;; expression keywords
   [(:or "fn" "λ") 'LAMBDA] ["let" 'LET] ["in" 'IN] ["case" 'CASE]
   ["fix" 'FIX] ["is" 'IS]
   ["if" 'IF] ["then" 'THEN] ["else" 'ELSE]
   ["when" 'WHEN] ["unless" 'UNLESS]
   ["for"   'FOR]
   [(:or "in?" "∈?") 'IN?]
   [(:or "empty" "ε") 'EMPTY]
   ["lub"   'LUB]
   ["true"  'TRUE] ["false" 'FALSE]

   ;; identifiers. this must come last so that we prefer to lex things as
   ;; keywords than as identifiers.
   [(:: (:& alphabetic lower-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-id (string->symbol lexeme))]
   [(:: (:& alphabetic upper-case)
        (:* (:or alphabetic numeric (char-set "_"))))
    (token-Id (string->symbol lexeme))]))
