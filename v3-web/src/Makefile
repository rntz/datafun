.PHONY: all repl clean sparkling remake FORCE

all: FORCE
	dune build datafun.cma

repl: FORCE
	dune utop .

clean:

sparkling: clean
	rm -rf _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
