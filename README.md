# rntztex

[latexrun]: https://github.com/aclements/latexrun

This is a collection of tools I (Michael Arntzenius) use for my LaTeX projects.
It contains:

1. A Makefile for LaTex projects that's short and fairly generic. It uses
   aclement's wonderful [latexrun][] tool, which is included as a git submodule.
   As soon as you clone my repo, you'll probably want to run:

   ```
   $ git submodule init && git submodule update
   ```

   This pulls down latexrun; no other installation necessary.

2. A LaTeX document class, `rntz`, and some latex packages:

   - `rntzgeometry`, which has geometry presets for various paper sizes.

   - `rntzfont`, which chooses between some nice fonts.

   - `narrow`, which sets up a one-column layout with extra width for `figure*`
     and `fullwidth` environments. `rntzgeometry` uses `narrow` automatically,
     but if you want to you can use `narrow` on its own.
