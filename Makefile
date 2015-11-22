# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
#PANDOC:=pandoc --latex-engine=xelatex
PANDOC:=pandoc --standalone

SOURCES:=system.md
OUTPUTS=$(SOURCES:.md=.pdf) $(SOURCES:.md=.tex)

.PHONY: all
all: system.pdf

%.pdf: %.md
	$(PANDOC) $< -o $@

%.tex: %.md
	$(PANDOC) $< -o $@

%.html: %.md
	$(PANDOC) $< -o $@

clean:
	rm -f $(OUTPUTS)
