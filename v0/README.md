# README

`repl.rkt` has a function `(repl)` that launches the Datafun repl. So, do
something like:

```
$ racket
Welcome to Racket v6.10.1.
> ;; Now you're in the racket repl. comments begin with semicolons.
  ;; Let's load "repl.rkt"!
  (require "repl.rkt")
> ;; Now we've loaded it, so we can call (repl) to get a Datafun repl.
  (repl)
- DF> (* now you're in the Datafun repl! comments look like this. *)
- DF> 2 + 2
4 : nat
- DF> (* we can quit the datafun repl by entering :quit all on its own *)
- DF> :quit
> ;; now we're back in Racket
  ;; we can quit Racket by entering ,quit
  ,quit
$ 
```

As of 2018-02-06, there appear to be some kinks in the repl that make it print
excess newlines, and also initialize with two prompts `- DF> - DF>`. I'm not
sure what's up with that. Sorry.

`raco make repl.rkt` precompiles everything so it launches faster. Run `rm -r
compiled` if you run into problems because your version of Racket has changed
since you last compiled, or similar.
