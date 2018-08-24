AGDAS := $(shell find . -iname '*.agda' '!' -name All.agda '!' -name '.*')

.PHONY: clean FORCE
deps.pdf: deps.dot
	filter-agda-dependency-graph <$< | dot -Tpdf >$@

deps.svg: deps.dot
	filter-agda-dependency-graph <$< | dot -Tsvg >$@

deps.dot: makeDeps.sh $(AGDAS)
	./makeDeps.sh >$@

clean:
	rm -f deps.pdf deps.svg deps.dot

# This makes files get deleted if the rule trying to build them fails. This
# prevents a following run of `make` from assuming the file is up-to-date.
.DELETE_ON_ERROR:

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
