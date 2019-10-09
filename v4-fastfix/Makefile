.PHONY: all project repl compile clean

all: project benchmark test/rplus.hs test/trans.hs

project:
	dune build datafun.cma compile.exe run.exe

test/%.hs: test/% project
	_build/default/compile.exe < $< >$@

repl: project
	rlwrap _build/default/run.exe

compile: project
	_build/default/compile.exe

benchmark: benchmark.hs Runtime.hs
	ghc --make $@

clean:
	dune clean
	rm -f benchmark *.hi *.o test/*.hs
