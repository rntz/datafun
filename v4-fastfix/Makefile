.PHONY: repl
repl:
	dune build run.exe
	rlwrap _build/default/run.exe

tests: $(wildcard *.hs)
	ghc --make $@

.PHONY: clean
clean:
	rm -f *.hi *.o
