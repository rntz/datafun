# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
PANDOC:=pandoc --standalone
PANDOC_TEX=--include-in-header header.sty

SOURCES:=system.md
OUTPUTS=$(SOURCES:.md=.pdf) $(SOURCES:.md=.tex)

.PHONY: all
all: system.pdf

%.pdf: %.md
	$(PANDOC) $(PANDOC_TEX) $< -o $@

%.tex: %.md
	$(PANDOC) $(PANDOC_TEX) $< -o $@

%.html: %.md
	$(PANDOC) $< -o $@

clean:
	rm -f $(OUTPUTS)
