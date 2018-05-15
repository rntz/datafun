RNTZTEXDIR := ./rntztex
LATEXRUN := $(RNTZTEXDIR)/latexrun/latexrun
# Tell TeX where to find things.
export TEXINPUTS := $(RNTZTEXDIR):

# Which tex files to build.
TEXS  := tones.tex tonal-linear-sequent-calculus.tex
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

# pdfbook combines pages to make a zine-style booklet. For example, if foo.pdf
# is formatted for A5 paper, foo-book.pdf will be A4. You can print it out, cut
# or fold down the middle, and staple the pages together.
%-book.pdf: %.pdf
	pdfbook $<

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
