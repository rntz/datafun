.PHONY: FORCE repl clean

_build/default/run.exe: FORCE
	dune build run.exe

repl: _build/default/run.exe
	rlwrap _build/default/run.exe

tests: $(wildcard *.hs)
	ghc --make $@

clean:
	rm -f *.hi *.o
