.PHONY: all repl clean sparkling remake FORCE

all: FORCE
	jbuilder build datafun.cma

repl: FORCE
	jbuilder utop .

clean:

sparkling: clean
	rm -rf _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
