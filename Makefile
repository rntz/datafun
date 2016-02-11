# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
PANDOC:=pandoc --standalone
PANDOC_TEX:=--include-in-header rntz.sty --variable=geometry:margin=1in

SOURCES:=$(wildcard system*.md)
AUXIL:=$(wildcard *.sty) Makefile
PDFS:=$(addsuffix .pdf,$(basename $(SOURCES)))

.PHONY: all watch
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(SOURCES) $(AUXIL); do make all; done

%.pdf: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

%.tex: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

clean:
	rm -f *.pdf

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
