# Overview

[latexrun]: https://github.com/aclements/latexrun

rntztex is a collection of tools I (Michael Arntzenius) use for my LaTeX
projects. It contains:

1. A Makefile for LaTeX projects that's short and fairly generic. It uses Austin
   Clements' wonderful [latexrun][] tool, which is included; no installation
   necessary. You will need Python 3 installed, however.

2. `rntz.cls`, a document class based on `extarticle` with some formatting
   changes. Most notably, it puts section numbers into the left-margin.

3. `rntzfont.sty`, which chooses between some nice font combinations.

4. `rntzgeometry.sty`, which sets margins etc. appropriately for common paper
   sizes.

5. `narrow.sty`, which sets up a one-column layout with extra width for
   `figure*` and `fullwidth` environments.

# Using rntztex

The easiest way to use this repo is to clone or copy it, put some `.tex` files
in it, and run `make`. That's all it takes!

Alternatively, you can keep rntztex in its own directory. This keeps your work
separate from mine, and lets you update rntztex easily. In this case, you should
copy the included `Makefile` to your source directory and update its
`RNTZTEXDIR` variable to contain the path to rntztex.

If you use git, you could use rntztex as a submodule, but submodules are a bit
complicated and beyond the scope of this README. Good luck!

# Licensing

This repo is currently MIT-licensed; see the LICENSE file. If you want to reuse
my code but you're worried about licensing issues, send me an email or a pull
request; I want this to be useful to as many people as possible.

# Files

## Makefile

Should be fairly self-documenting. Let me know if you have any trouble with it.
Useful targets:

- `make all`: Makes PDFs for every `.tex` file in its directory. Does not look
  in subdirectories.

- `make watch`: Watches for changes and recompiles on-the-fly. Uses
  `inotifywait`, which is in the `inotify-tools` package on Ubuntu.

- `make foo.pdf`: Makes a PDF from `foo.tex`.

- `make foo-book.pdf`: Makes a zine-style "booklet" from a regular PDF. For
  example, if `foo.pdf` is formatted for A5 paper, `foo-book.pdf` will be A4,
  with two pages per side. You can print it out, cut or fold down the middle,
  and staple the pages together. Needs the `pdfbook` tool.

- `make foo-2up.pdf`: Like `make foo-book.pdf` but makes a 2-up version. Needs
  the `pdfjam` tool.

- `make clean`: Runs `latexrun --clean-all` and also removes `latex.out` (where
  `latexrun` stores intermediate files).

## rntz.cls

Based on extarticle, and supports most of its options. Notable differences:

1. Section & sub-section numbers go into the left margin.
2. Sections & sub-sections headings are smaller.
3. Sub-sub-sections are un-numbered; I use them sparingly if at all.
4. Redefines `\maketitle` and the `abstract` environment.

It also has a somewhat random grab-bag of other features I happen to use:

5. Requires and configures hyperref, url, and cleveref.

6. Requires amsmath & amsthm, and defines theorem, conjecture, lemma,
definition, and corollary environments. It sets them to share a single running
counter.

7. Defines some colors, taken from acmart.cls:
ACM{Blue,Yellow,Orange,Red,LightBlue,DarkBlue,Green,Purple}.

## rntzgeometry.sty

Sets the page geometry to have "reasonable" margins. Options indicate paper
size: `a5`, `b5`, `a4`, `letter`. Default is `a4`.

## narrow.sty

This sets your body text in a single narrow column, but defines a `fullwidth`
environment that expands to "full width". It redefines `figure*` to use full
width as well.

**Options**:

- `width=LEN`: The width of the main text column. Default 345pt.

- `fullwidth=LEN`: The width for `figure*` and `fullwidth` environments. Default
  is `\textwidth`, i.e. the width the text *would have been* before you loaded
  `narrow.sty`.

## rntzfont.sty

This chooses from a set of fonts, with matched x-heights and reasonable line
spacings. The text font options are named by the serif font they choose. Most
load [Biolinum][Libertine] for sans-serif, and all load [Inconsolata][] for
monospace. The text fonts are:

- `alegreya` for [Alegreya Serif and Sans][alegreya], a strongly-flavored,
  rather angular font.

- `baskervald` for [Baskervald][baskervaldx], a Baskerville variant. Nice in
  print, acceptable on screen.

- `charter` for [Bitstream Charter][charter] with [Source Sans Pro][ssans].
  Charter is very legible, even at low DPI.

- `cochineal` for [Cochineal][]. Cochineal is an old-style font, pleasant in
   print and tolerable on screen.

- `libertine` for [Linux Libertine][Libertine]. Libertine has similar metrics to
  Times New Roman. It works well with [newtxmath][].

- `librebaskerville` for [Libre Baskerville][librebaskerville], a Baskerville
  revival designed for screen use. It lacks small caps and has "faked" bold
  italics.

- `palatino` for [Palatino][], an elegant font that still displays well on
  screen. Palatino and Euler are both designed by Hermann Zapf, and match
  nicely.

- `pt` for [PT Serif and Sans][pt]. PT Serif is very readable on screen and at
  low DPI. However, its LaTeX package is missing some features, such as small
  caps and straight quotes.

- `source` for [Source Serif Pro][sserif] with [Source Sans Pro][ssans]. Source
  Serif is a very legible font, similar to Charter, with more fine details in
  print. However, the version distributed with TeX Live 2018 (and prior) lacks
  italics.

You can also choose between three families of math fonts:

- `euler` for [Euler][], a somewhat calligraphic upright math font.

- `newmath` for [newtxmath][] (or its relative [newpxmath][]), using whichever
  variant most nicely matches the text font choice.

- `nomath` leaves the math font unchanged.

The defaults are `charter` with `euler`.

Many thanks to [Michael Sharpe](http://math.ucsd.edu/~msharpe/), who maintains
the Baskervaldx, cochineal, inconsolata, newtx, newpx, and xcharter packages;
and to Bob Tennent, who maintains the alegreya, librebaskerville, and libertine
packages.

[alegreya]: https://ctan.org/pkg/alegreya
[baskervaldx]: https://ctan.org/pkg/baskervaldx
[librebaskerville]: https://ctan.org/pkg/librebaskerville
[Cochineal]: https://ctan.org/pkg/cochineal
[Euler]: https://ctan.org/pkg/eulervm
[Inconsolata]: https://ctan.org/pkg/inconsolata
[Libertine]: https://ctan.org/pkg/libertine
[Palatino]: https://ctan.org/pkg/newpx
[charter]: https://ctan.org/pkg/XCharter
[pt]: https://ctan.org/pkg/paratype
[newtxmath]: https://ctan.org/pkg/newtx
[newpxmath]: https://ctan.org/pkg/newpx
[ssans]: https://ctan.org/pkg/sourcesanspro
[sserif]: https://ctan.org/pkg/sourceserifpro

## example.tex

A simple example document showing off `rntz.cls`, `rntzgeometry.sty`, and
`rntzfont.sty`.

## xheight.tex

A test document used to check x-heights are aligned across different fonts.
