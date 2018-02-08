.PHONY: all watch clean sparkling remake FORCE

all: FORCE
	jbuilder build datafun.cma

clean:

sparkling: clean
	rm -rf _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
