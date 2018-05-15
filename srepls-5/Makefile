# If you use latexmk, you might like to put this line in your ~/.latexmkrc:
# $pdflatex = 'pdflatex -interaction=nonstopmode';
# it makes latexmk quit on compilation failure.

TEXS    := slides.tex
# other things which affect compilation result
DEPENDS := Makefile $(wildcard *.sty)

PDFS   := $(TEXS:.tex=.pdf)
JUNK   := $(TEXS:.tex=.dvi) $(TEXS:.tex=.bbl)
JUNK   += $(TEXS:.tex=.snm) $(TEXS:.tex=.nav) $(TEXS:.tex=.vrb)

.PHONY: all watch view clean
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(TEXS) $(DEPENDS); do make all; done

clean:
	latexmk -c
	rm -f $(PDFS) $(JUNK)

%.pdf: %.tex $(DEPENDS)
	latexmk --pdf $<
	# pdflatex $<
	# rubber --pdf $<

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
