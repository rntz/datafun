\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntz}[2018/03/19]

\RequirePackage{etoolbox}       % toggles; fixing titlesec.
\newtoggle{narrow}              % stick to a 12cm central column?
\newtoggle{centertitle}         % center titles?
\newtoggle{geometry}            % configure geometry?
\newtoggle{ribbons}             % colored section number ribbons?

%% TODO: use more Tufte-css-like font sizes, then:
%% change \section to be \Large, \subsection to \large
%% change author,date to be \large
%% and check that all this still works on a5.

%% TODO: consider factoring out some of this into a .sty file:
%% - narrowing!
%% - the newtheorem stuff
%% - colors
%% - hyperref & hypersetup
%% - the left-margin colored section numbers

%% ---- Options ----
\DeclareOption{narrow}{\toggletrue{narrow}}
\DeclareOption{wide}{\togglefalse{narrow}}
\DeclareOption{centertitle}{\toggletrue{centertitle}}
\DeclareOption{nocentertitle}{\togglefalse{centertitle}}
\DeclareOption{ribbons}{\toggletrue{ribbons}}
\DeclareOption{noribbons}{\togglefalse{ribbons}}
\DeclareOption{geometry}{\toggletrue{geometry}}
\DeclareOption{nogeometry}{\togglefalse{geometry}}

\DeclareOption{zapf}{\def\rntz@font{zapf}}
\DeclareOption{libertine}{\def\rntz@font{libertine}}
\DeclareOption{cm}{\def\rntz@font{cm}}

%     a5: 148 x 210mm    5.8 x  8.3in
%     b5: 176 x 250mm    6.9 x  9.8in
%     a4: 210 x 297mm    8.3 x 11.7in
% letter: 216 x 279mm    8.5 x 11in
\DeclareOption{a5}{
  \def\rntz@geom{a5paper,text={345pt,17cm}}
  \def\rntz@narrow{104mm}}
\DeclareOption{b5}{
  \def\rntz@geom{b5paper,text={135mm,200mm}}
  \def\rntz@narrow{345pt}}
\DeclareOption{a4}{
  \def\rntz@geom{a4paper,text={160mm,240mm}}
  \def\rntz@narrow{345pt}}
\DeclareOption{letter}{
  \def\rntz@geom{letterpaper,text={166mm,222mm}}
  \def\rntz@narrow{345pt}}

\DeclareOption{twocolumn}{\ClassWarning{rntz}{Two-column mode is not supported.}}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}

% Defaults
\ExecuteOptions{b5,zapf,geometry,narrow}
\ProcessOptions\relax

%% ---- Basic layout ----
\LoadClass{extarticle}
\iftoggle{geometry}{\RequirePackage[\rntz@geom]{geometry}}
  %% We can't do a narrow column if we don't understand the geometry.
  {\togglefalse{narrow}}

%% if narrow, limit text width to 12cm - article.cls' default width on a4?
\iftoggle{narrow}{
  \newlength{\rntz@fulltextwidth}
  \setlength{\rntz@fulltextwidth}{\textwidth}
  \geometry{textwidth=\rntz@narrow}}{}

%% ---- figure* for wide figures in narrow mode ----
%% First, define a fullwidth environment.
\iftoggle{narrow}{
  \RequirePackage[strict]{changepage}
  %% I want to go from \textwidth to \rntz@fulltextwidth. adjustwidth adds to
  %% margins, subtracting from text width, so I should adjust by:
  %% (\textwidth-\rntz@fulltextwidth)/2.
  \newlength{\rntz@fullwidthoffset}
  \setlength{\rntz@fullwidthoffset}{\dimexpr(\textwidth-\rntz@fulltextwidth)/2\relax}
  \newenvironment{fullwidth}
    {\begin{adjustwidth}{\the\rntz@fullwidthoffset}{\the\rntz@fullwidthoffset}}
    {\end{adjustwidth}}
}
% in wide mode, fullwidth does nothing
{ \newenvironment{fullwidth}{}{} }

%% A hack, taken from https://stackoverflow.com/questions/1565988/making-a-small-modification-to-a-latex-environment
\renewenvironment{figure*}[1][\fps@figure]
  {\edef\@tempa{\noexpand\@float{figure}[#1]}%
   \@tempa\begin{fullwidth}\centering}
  {\end{fullwidth}\end@float}

%% ---- AMS stuff and theorem styles ----
%% This must precede \RequirePackage{newtxmath}; otherwise newtxmath defines
%% \openbox and amsthm crashes complaining \openbox is already defined.
\RequirePackage{amsthm,amsmath,amssymb}

%% Everything is numbered sequentially with a single counter.
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem{conjecture}[theorem]{Conjecture}
\newtheorem{lemma}[theorem]{Lemma}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem*{corollary}{Corollary}
\theoremstyle{plain}            %back to default

%% ---- Fonts ----
\ifdefstring{\rntz@font}{libertine}{
  \RequirePackage[mono=false]{libertine} % osf = old-style figures
  \RequirePackage[libertine]{newtxmath}  % makes math look prettier
  \linespread{1.1}
}{}

\ifdefstring{\rntz@font}{zapf}{
  \RequirePackage{mathpazo}
  \RequirePackage{eulervm}
  \linespread{1.15}
}{}

%% ---- Styling paragraphs and lists ----
\setlength{\parindent}{1.0pc}
\RequirePackage{enumitem}           % list styling
\setlist{noitemsep,topsep=\smallskipamount}

%% ---- Title formatting and sizing ----
\newcommand{\titlesize}{\Large}
\newcommand{\authorsize}{\normalsize}
\newcommand{\secsize}{\large}
\newcommand{\subsecsize}{\normalsize}
\newcommand{\subsubsecsize}{\normalsize}

%% TODO: omit {title,author,date} if not provided
%% TODO: support \subtitle.
\RequirePackage{placeins}       % for \FloatBarrier
\renewcommand*{\maketitle}{
  \begingroup%
  \setlength{\parindent}{0pt}%
  \iftoggle{centertitle}{\centering}{}%
  {\titlesize\@title\vspace{0.5ex}\par}%
  {\authorsize\@author\vspace{0.5ex}\par}%
  {\authorsize\@date\par}%
  \endgroup\FloatBarrier}

%% ---- Abstracts ----
%% TODO.

%% ---- Colors ----
\RequirePackage[dvipsnames]{xcolor}
\definecolor[named]{ACMBlue}{cmyk}{1,0.1,0,0.1}
\definecolor[named]{ACMYellow}{cmyk}{0,0.16,1,0}
\definecolor[named]{ACMOrange}{cmyk}{0,0.42,1,0.01}
\definecolor[named]{ACMRed}{cmyk}{0,0.90,0.86,0}
\definecolor[named]{ACMLightBlue}{cmyk}{0.49,0.01,0,0}
\definecolor[named]{ACMGreen}{cmyk}{0.20,0,1,0.19}
\definecolor[named]{ACMPurple}{cmyk}{0.55,1,0,0.15}
\definecolor[named]{ACMDarkBlue}{cmyk}{1,0.58,0,0.21}

%% ---- Hyperlinks ----
\RequirePackage{hyperref,url}
\hypersetup{colorlinks,linkcolor=ACMRed,citecolor=ACMPurple,urlcolor=ACMDarkBlue,filecolor=ACMDarkBlue}

%% ---- Section & subsection titles ----
\RequirePackage{textcase,titlesec}    % (sub)section header styling

\titlespacing*{\section}{0pt}{15pt}{10pt}
%% \titlespacing*{\subsection}{0pt}{12pt}{6pt}
\titlespacing*{\subsection}{0pt}{12pt}{8pt}
\titlespacing*{\subsubsection}{0pt}{12pt}{8pt}

%% titlesec < 2.10.2 has a bug that prevents showing section numbers. This fixes
%% it. Taken from
%% https://tex.stackexchange.com/questions/96090/formatting-subsections-and-chapters-in-tufte-book/96125
\patchcmd{\ttlh@hang}{\parindent\z@}{\parindent\z@\leavevmode}{}{}
\patchcmd{\ttlh@hang}{\noindent}{}{}{}

%% Spacing.
%% TODO: maybe this should depend on paper size?
\newcommand{\hnopost}{\hspace*{0mm}}
\newcommand{\hnopre}{\hspace*{2.5mm}}
\newcommand{\header}{\rmfamily\bfseries}
%% \renewcommand{\header}{\rmfamily\itshape} % previously
\newcommand{\hno}[1]{\colorhno{white}{black}{#1}}

\iftoggle{ribbons}
  {\newcommand{\colorhno}[3]%
    {\llap{\colorbox{#1}{\parbox{100in}{\hfill{\color{#2}#3\hnopost}}}\hnopre}}}
  {\newcommand{\colorhno}[3]{%
    {\llap{\colorbox{white}{\parbox{100in}{\hfill{#3\hnopost}}\hnopre}}}}}

% Nice colors: Periwinkle, Whee, cyan
\definecolor[named]{Whee}{cmyk}{0.33, 0.33, 0, 0}
\titleformat{\section}{\secsize\header}
            {\colorhno{Periwinkle}{white}{\thesection}}{0pt}{}
\titleformat{\subsection}{\subsecsize\header}{\hno{\thesubsection}}{0pt}{}
\titleformat{\subsubsection}{\subsubsecsize\header}{\hno{\thesubsubsection}}{0pt}{}
%% %% Uncomment for orange subsection ribbons.
%% \titleformat{\subsection}{\subsecsize\header}
%%             {\colorhno{ACMOrange}{white}{\thesubsection}}{0pt}{}


%% %% Tufte font sizes.
%% \renewcommand{\titlesize}{\LARGE}
%% \renewcommand{\authorsize}{\large}
%% \renewcommand{\secsize}{\Large}
%% \renewcommand{\subsecsize}{\large}

%% \linespread{1}

%% \renewcommand\normalsize{%
%%    \@setfontsize\normalsize\@xpt{14}%
%%    \abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@
%%    \abovedisplayshortskip \z@ \@plus3\p@
%%    \belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@
%%    \belowdisplayskip \abovedisplayskip
%%    \let\@listi\@listI}
%% \normalbaselineskip=14pt
%% \normalsize
%% \renewcommand\small{%
%%    \@setfontsize\small\@ixpt{12}%
%%    \abovedisplayskip 8.5\p@ \@plus3\p@ \@minus4\p@
%%    \abovedisplayshortskip \z@ \@plus2\p@
%%    \belowdisplayshortskip 4\p@ \@plus2\p@ \@minus2\p@
%%    \def\@listi{\leftmargin\leftmargini
%%                \topsep 4\p@ \@plus2\p@ \@minus2\p@
%%                \parsep 2\p@ \@plus\p@ \@minus\p@
%%                \itemsep \parsep}%
%%    \belowdisplayskip \abovedisplayskip
%% }
%% \renewcommand\footnotesize{%
%%    \@setfontsize\footnotesize\@viiipt{10}%
%%    \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
%%    \abovedisplayshortskip \z@ \@plus\p@
%%    \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
%%    \def\@listi{\leftmargin\leftmargini
%%                \topsep 3\p@ \@plus\p@ \@minus\p@
%%                \parsep 2\p@ \@plus\p@ \@minus\p@
%%                \itemsep \parsep}%
%%    \belowdisplayskip \abovedisplayskip
%% }

%% \renewcommand\scriptsize{\@setfontsize\scriptsize\@viipt\@viiipt}
%% \renewcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
%% \renewcommand\large{\@setfontsize\large\@xipt{15}}
%% \renewcommand\Large{\@setfontsize\Large\@xiipt{16}}
%% \renewcommand\LARGE{\@setfontsize\LARGE\@xivpt{18}}
%% \renewcommand\huge{\@setfontsize\huge\@xxpt{30}}
%% \renewcommand\Huge{\@setfontsize\Huge{24}{36}}
