LATEXRUN := ../latexrun/latexrun

TEXS    := datafun.tex expansions.tex presentation.tex
# other things which affect compilation result
DEPENDS := Makefile datafun.bib sigplanconf.cls
DEPENDS += $(wildcard *.sty) $(wildcard *.tex)

PDFS   := $(TEXS:.tex=.pdf)
JUNK   := $(TEXS:.tex=.dvi) $(TEXS:.tex=.bbl)
JUNK   += $(TEXS:.tex=.snm) $(TEXS:.tex=.nav)

.PHONY: all watch clean
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(TEXS) $(DEPENDS); do make all; done

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out
#	rm -f $(PDFS) $(JUNK)

%.pdf: %.tex $(DEPENDS)
	$(LATEXRUN) $<

sources.zip: $(DEPENDS)
	rm -f $@
	zip $@ $^

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
