.PHONY: all watch clean sparkling FORCE
all: datafun.top

datafun.top: FORCE
	ocamlbuild -verbose 1 $@

clean:
	rm -f datafun.top

sparkling: clean
	rm -r _build

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
