.PHONY: all watch clean sparkling remake FORCE

all: FORCE
	opam config exec -- ocamlbuild datafun.top datafun.cma

clean:
	rm -f datafun.top

sparkling: clean
	rm -rf _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
