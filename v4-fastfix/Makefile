.PHONY: all ocaml tests benchmarks run-benchmarks repl compile clean FORCE

all: ocaml tests benchmarks

# The Datafun repl & compiler, in ocaml.
_build/default/seminaive.exe: ocaml
_build/default/seminaive_raw.exe: ocaml
_build/default/seminaive_simple.exe: ocaml
_build/default/naive.exe: ocaml
_build/default/run.exe: ocaml
ocaml:
	dune build datafun.cma run.exe naive.exe seminaive.exe seminaive_raw.exe seminaive_simple.exe

repl: _build/default/run.exe
	rlwrap _build/default/run.exe
compile: _build/default/seminaive.exe
	_build/default/seminaive.exe

# Compiling Datafun to Haskell.
TESTS=$(wildcard test/*.df)
HSTESTS=$(TESTS:.df=-naive.hs) $(TESTS:.df=-seminaive.hs) $(TESTS:.df=-seminaive-raw.hs) $(TESTS:.df=-seminaive-simple.hs)
tests: $(HSTESTS)
test/%-naive.hs: test/%.df _build/default/naive.exe
	_build/default/naive.exe < $< >$@
test/%-seminaive.hs: test/%.df _build/default/seminaive.exe
	_build/default/seminaive.exe < $< >$@
test/%-seminaive-raw.hs: test/%.df _build/default/seminaive_raw.exe
	_build/default/seminaive_raw.exe < $< >$@
test/%-seminaive-simple.hs: test/%.df _build/default/seminaive_simple.exe
	_build/default/seminaive_simple.exe < $< >$@

# The benchmarks. NBENCH is the number of different input sizes to test on (the
# number of different data points we'll get on the x-axis of the graph).
BENCHES := trans astar astar2
BENCH_PROGS := $(addprefix benchmark-,$(BENCHES))
BENCH_DATS := $(addsuffix .dat,$(BENCHES))
NBENCH ?= 12
benchmarks: $(BENCH_PROGS)
run-benchmarks: $(BENCH_DATS)
benchmark-%: benchmark-%.hs Benchmark.hs Runtime.hs
	ghc -O2 --make $@
%.dat: benchmark-% FORCE
	./$< $(NBENCH) | tee $@

# The graph pdf. I don't want building graph.pdf to force re-running the
# benchmarks, because that takes a while, so I don't list trans.dat and
# regex.dat as dependencies, but I do test they exist.
RNTZTEXDIR := ../rntztex/
export TEXINPUTS := $(RNTZTEXDIR):
LATEXRUN := $(RNTZTEXDIR)/latexrun/latexrun
graph.pdf: graph.tex FORCE
	test -f trans.dat
	test -f astar.dat
	test -f astar2.dat
	$(LATEXRUN) $<

# Cleanup
clean:
	dune clean
	rm -f graph.pdf *.hi *.o $(BENCH_PROGS) test/*.hs

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
