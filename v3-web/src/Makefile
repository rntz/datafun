.PHONY: all repl clean sparkling remake FORCE

all: FORCE
	dune build datafun.cma

utop: FORCE
	dune utop .

repl: FORCE
	dune build run.exe
	rlwrap _build/default/run.exe

clean:

sparkling: clean
	rm -rf _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
