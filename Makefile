# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
PANDOC:=pandoc --standalone
PANDOC_TEX:=--include-in-header header.sty --variable=geometry:margin=1in

SOURCES:=README.md system.md system-posets-2layer.md
AUXIL:=$(wildcard *.sty) Makefile
OUTPUTS=$(SOURCES:.md=.pdf) $(SOURCES:.md=.tex)

.PHONY: all watch
all: system.pdf system-posets.pdf
watch: all
	@while inotifywait -e modify $(SOURCES) $(AUXIL); do make all; done

%.pdf: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

%.tex: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

clean:
	rm -f $(OUTPUTS)
