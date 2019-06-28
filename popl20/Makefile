# Path to latexrun.
LATEXRUN := ../rntztex/latexrun/latexrun

# By default, try to build every tex file in this directory.
# Customize $(TEXS) to change this.
TEXS  := seminaive.tex # $(wildcard *.tex)
PDFS  := $(addsuffix .pdf,$(basename $(TEXS)))

.PHONY: all watch clean FORCE
all: $(PDFS)

# If you have inotify-tools, this will automatically recompile your pdfs "live".
# It's a bit overenthusiastic, though; it reruns `make` when ANYTHING changes.
watch: all
	@while inotifywait -e modify -r . >/dev/null 2>&1; do \
		echo; \
		make --no-print-directory -j all; \
	done

%.pdf: %.tex FORCE
	$(LATEXRUN) $<

clean:
	$(LATEXRUN) --clean-all
	rm -r latex.out

# debugging: `make print-FOO` will print the value of $(FOO)
.PHONY: print-%
print-%:
	@echo $*=$($*)
