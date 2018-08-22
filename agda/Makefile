AGDAS := $(shell find . -iname '*.agda' '!' -name All.agda '!' -name '.*')

.PHONY: FORCE
deps.pdf: deps.dot
	filter-agda-dependency-graph <$< | dot -Tpdf >$@

deps.dot: All.agda
	agda --allow-unsolved-metas $< --dependency-graph=$@

All.agda: $(AGDAS)
	./makeAll.agda.sh

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)

