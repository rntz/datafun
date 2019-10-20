TESTS=$(wildcard test/*.df)
HSTESTS=$(TESTS:.df=-naive.hs) $(TESTS:.df=-seminaive.hs)

.PHONY: all tests ocaml repl compile clean FORCE

all: ocaml tests benchmark

ocaml:
	dune build datafun.cma naive.exe seminaive.exe run.exe
_build/default/seminaive.exe: ocaml
_build/default/naive.exe: ocaml
_build/default/run.exe: ocaml

repl: _build/default/run.exe
	rlwrap _build/default/run.exe

compile: _build/default/seminaive.exe
	_build/default/seminaive.exe

tests: $(HSTESTS)
test/%-naive.hs: test/%.df _build/default/naive.exe
	_build/default/naive.exe < $< >$@
test/%-seminaive.hs: test/%.df _build/default/seminaive.exe
	_build/default/seminaive.exe < $< >$@

benchmark: benchmark.hs Runtime.hs
	ghc -O2 --make $@

clean:
	dune clean
	rm -f benchmark *.hi *.o test/*.hs

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
