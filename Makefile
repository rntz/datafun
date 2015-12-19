# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
PANDOC:=pandoc --standalone
PANDOC_TEX:=--include-in-header header.sty --variable=geometry:margin=1in

SOURCES:=$(wildcard *.md)
AUXIL:=$(wildcard *.sty) Makefile
OUTPUTS=$(addsuffix .pdf,$(basename $(SOURCES)))

.PHONY: all watch
all: system.pdf system-posets.pdf system-posets-2layer.pdf
watch: all
	@while inotifywait -e modify $(SOURCES) $(AUXIL); do make all; done

%.pdf: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

%.tex: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

clean:
	rm -f $(OUTPUTS)

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
