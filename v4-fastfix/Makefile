.PHONY: all tests ocaml repl compile clean FORCE

all: ocaml tests benchmark-trans benchmark-regex

clean:
	dune clean
	rm -f benchmark-trans benchmark-regex graph.pdf *.hi *.o test/*.hs

# The Datafun repl & compiler, in ocaml.
_build/default/seminaive.exe: ocaml
_build/default/naive.exe: ocaml
_build/default/run.exe: ocaml
ocaml:
	dune build datafun.cma naive.exe seminaive.exe run.exe

repl: _build/default/run.exe
	rlwrap _build/default/run.exe
compile: _build/default/seminaive.exe
	_build/default/seminaive.exe

# Compiling Datafun to Haskell.
TESTS=$(wildcard test/*.df)
HSTESTS=$(TESTS:.df=-naive.hs) $(TESTS:.df=-seminaive.hs)
tests: $(HSTESTS)
test/%-naive.hs: test/%.df _build/default/naive.exe
	_build/default/naive.exe < $< >$@
test/%-seminaive.hs: test/%.df _build/default/seminaive.exe
	_build/default/seminaive.exe < $< >$@

# The benchmarks. NBENCH is one more than the number of benchmarks to run. For
# example, NBENCH=12 means we'll run benchmarks on 11 distinct input sizes.
NBENCH ?= 12
benchmark-%: benchmark-%.hs Benchmark.hs Runtime.hs
	ghc -O2 --make $@
%.dat: benchmark-%
	./$< | tee $@ | head -n$(NBENCH)

# The graph pdf. I don't want building graph.pdf to force re-running the
# benchmarks, so I don't list trans.dat and regex.dat as dependencies.
RNTZTEXDIR := ../rntztex/
export TEXINPUTS := $(RNTZTEXDIR):
LATEXRUN := $(RNTZTEXDIR)/latexrun/latexrun
graph.pdf: graph.tex FORCE
	$(LATEXRUN) $<

# Automatic recompilation.
.PHONY: watch watch\:%
watch: watch\:all
watch\:%: %
	@while inotifywait -e modify -r . >/dev/null 2>&1; do \
		echo; \
		make --no-print-directory -j $^; \
	done

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
