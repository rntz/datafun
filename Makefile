LATEXRUN := ./latexrun/latexrun

TEXS  := tones.tex tonal-linear-sequent-calculus.tex
# other things which affect compilation result
AUXIL := $(wildcard *.sty *.cls) Makefile
PDFS  := $(addsuffix .pdf,$(basename $(TEXS)))

.PHONY: all watch clean FORCE
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(TEXS) $(AUXIL) >/dev/null 2>&1; do \
		echo; \
		make --no-print-directory -j all; \
	done

%.pdf: %.tex FORCE
	$(LATEXRUN) $<

%-book.pdf: %.pdf
	pdfbook $<

%.tex: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
