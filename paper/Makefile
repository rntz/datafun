SOURCES := $(wildcard *.tex)
# also rerun if any of $(AUXIL) change
AUXIL   := Makefile datafun.bib sigplanconf.cls $(wildcard *.sty)

PDFS    := $(SOURCES:.tex=.pdf)
GARBAGE := $(SOURCES:.tex=.dvi) $(SOURCES:.tex=.bbl)

.PHONY: all watch clean
all: $(PDFS)
watch: all
	@while inotifywait -e modify $(SOURCES) $(AUXIL); do make all; done

clean:
	latexmk -c
	rm -f $(PDFS) $(GARBAGE)

%.pdf: %.tex $(AUXIL)
	latexmk --pdf $<
	# rubber --pdf $<

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
