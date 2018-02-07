.PHONY: all watch clean sparkling remake FORCE
all: datafun.top

datafun.top: FORCE
	ocamlbuild $@

clean:
	rm -f datafun.top

sparkling: clean
	rm -r _build

remake: sparkling
	make

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
