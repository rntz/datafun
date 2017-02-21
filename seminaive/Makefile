LATEXRUN := ./latexrun

TEXS    := seminaive.tex
# other things which affect compilation result
DEPENDS := Makefile $(wildcard *.sty)

.PHONY: all watch view clean FORCE
all: $(TEXS:.tex=.pdf)

watch: all
	@while inotifywait -e modify $(TEXS) $(DEPENDS); do make all; done

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

%.pdf: %.tex FORCE
	$(LATEXRUN) $<

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
