# If you use latexmk, you might like to put this line in your ~/.latexmkrc:
# $pdflatex = 'pdflatex -interaction=nonstopmode';
# it makes latexmk quit on compilation failure.

TEXS := $(wildcard *.tex)
# also rerun if any of $(AUXIL) change
AUXIL   := Makefile datafun.bib sigplanconf.cls $(wildcard *.sty)

PDFS    := $(TEXS:.tex=.pdf)
GARBAGE := $(TEXS:.tex=.dvi) $(TEXS:.tex=.bbl)

.PHONY: all watch view clean
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(TEXS) $(AUXIL); do make all; done

view:
	latexmk -pvc --pdf datafun.tex

clean:
	latexmk -c
	rm -f $(PDFS) $(GARBAGE)

%.pdf: %.tex $(AUXIL)
	latexmk --pdf $<
	# pdflatex $<
	# rubber --pdf $<

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
