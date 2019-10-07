.PHONY: all repl compile clean

all:
	dune build datafun.cma compile.exe run.exe

repl: all
	rlwrap _build/default/run.exe

compile: all
	_build/default/compile.exe

tests: $(wildcard *.hs)
	ghc --make $@

clean:
	rm -f *.hi *.o
