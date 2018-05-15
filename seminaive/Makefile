RNTZTEXDIR := ../rntztex
LATEXRUN := $(RNTZTEXDIR)/latexrun/latexrun
# Tell TeX where to find .sty and .cls files.
export TEXINPUTS := $(RNTZTEXDIR):

TEXS  := $(wildcard *.tex)
PDFS  := $(addsuffix .pdf,$(basename $(TEXS)))

.PHONY: all watch clean FORCE
all: $(PDFS)

watch: all
	@while inotifywait -e modify -r . >/dev/null 2>&1; do \
		echo; \
		make --no-print-directory -j all; \
	done

%.pdf: %.tex FORCE
	$(LATEXRUN) $<

%-book.pdf: %.pdf
	pdfbook $<

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
