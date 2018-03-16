LATEXRUN := ./latexrun/latexrun

TEXS  := tones.tex notes-test.tex tufte-test.tex
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

%.tex: %.md $(AUXIL)
	$(PANDOC) $(PANDOC_TEX) $< -o $@

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
