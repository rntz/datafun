.PHONY: all repl clean sparkling remake FORCE

all: FORCE
	jbuilder build --root=src datafun.cma

repl: FORCE
	jbuilder utop src

clean:

sparkling: clean
	rm -rf src/_build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
