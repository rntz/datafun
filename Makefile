# TODO: bibliography file
# pandoc --filter pandoc-citeproc $< --biblio BIBLIOFILE
#PANDOC:=pandoc --latex-engine=xelatex
PANDOC:=pandoc

%.pdf: %.md
	$(PANDOC) $< -o $@

%.tex: %.md
	$(PANDOC) $< -o $@

%.html: %.md
	$(PANDOC) $< -o $@
