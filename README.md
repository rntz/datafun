# Overview

[latexrun]: https://github.com/aclements/latexrun

This is a collection of tools I (Michael Arntzenius) use for my LaTeX projects.
It contains:

1. A Makefile for LaTex projects that's short and fairly generic. It uses
   aclement's wonderful [latexrun][] tool, which is included as a git submodule.
   After cloning this repo, you should run:

   ```
   $ git submodule init && git submodule update
   ```

   This pulls down latexrun (~315kb as of 2018-05-15); no other installation
necessary.

2. A LaTeX document class, `rntz.cls`, which is based on `extarticle`, but with
   some formatting changes. Most notably, it puts section numbers into the
   left-margin.

3. `rntzgeometry.sty`, which has geometry presets for various paper sizes.

4. `rntzfont.sty`, which chooses between some nice font combinations.

5. `narrow.sty`, which sets up a one-column layout with extra width for
   `figure*` and `fullwidth` environments. `rntzgeometry.sty` uses `narrow.sty`
   automatically, but if you want to you can use `narrow.sty` on its own.

# How to use this repo

If you want to use my tools in your project, here are two ways to go about it:

1. Clone or copy this repo, put your `.tex` files in it, and you're good!

2. Use this repo as a submodule of your actual project. This keeps your work
   separate from mine, and lets you stay up-to-date easily. In this case, you
   should copy the included `Makefile` to your source directory and update its
   `SUBMODULEDIR` variable to point to the submodule's path.

This repo is currently MIT-licensed. If you want to reuse my code but you're
worried about licensing issues, send me an email or a pull request; I want this
to be useful to as many people as possible.

# Files

## Makefile
Should be fairly self-documenting. Let me know if you have any trouble with it.

## example.tex

A simple example document showing off `rntz.cls`, `rntzgeometry.sty`, and
`rntzfont.sty`.

## rntz.cls
Based on extarticle, and supports most of its options. Notable differences:

1. Section & sub-section numbers go into the left margin.
2. Sections & sub-sections headings are smaller.
3. Sub-sub-sections are un-numbered; I use them sparingly if at all.
4. Redefines `\maketitle` and the `abstract` environment.
5. Fiddles with paragraph and list item spacing.

It also has a somewhat random grab-bag of other features I happen to use:

6. Requires and configures hyperref, url, and cleveref.

7. Requires amsmath & amsthm, and defines theorem, conjecture, lemma,
definition, and corollary environments. It sets them to share a single running
counter.

8. Defines some colors, taken from acmart.cls:
ACM{Blue,Yellow,Orange,Red,LightBlue,DarkBlue,Green,Purple}.

## rntzgeometry.sty
Sets the page geometry to have "reasonable" margins. It uses `narrow.sty` to
produce a single column of text; the `figure*` and `fullwidth` environments
expand to a larger width.

**Options**:

- `a5`, `b5`, `a4`, `letter`: Paper size. Default is b5.

- `width=LEN`: Width of the main text column. Default is 345pt.

- `fullwidth=LEN`: Width for `figure*` and `fullwidth` environments. Default
  varies by paper size.

## rntzfont.sty
This chooses from a set of paired text & math fonts, with appropriate scalings
and line spacings.

The options are `charter`, `cochineal`, `palatino`, `libertine`, `fourier`, and
`cm` (Computer Modern). Default is `palatino`.

## narrow.sty
This sets your body text in a single narrow column, but defines a `fullwidth`
environment that expands to "full width". It redefines `figure*` to use full
width as well.

**Options**:

- `width=LEN`: The width of the main text column. Default 345pt.

- `fullwidth=LEN`: The width for `figure*` and `fullwidth` environments. Default
  is `\textwidth`.
