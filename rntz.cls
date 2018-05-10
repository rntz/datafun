\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntz}[2018/03/19]

\RequirePackage{etoolbox}       % toggles; fixing titlesec.
\newtoggle{ribbons}             % colored section number ribbons?

%% TODO: consider factoring out some of this into a .sty file:
%% DONE - narrowing! in narrow.sty.
%% - the newtheorem stuff
%% - colors
%% - hyperref & hypersetup
%% - the left-margin colored section numbers

%% ---- Options ----
\DeclareOption{ribbons}{\toggletrue{ribbons}}
\DeclareOption{noribbons}{\togglefalse{ribbons}}

\DeclareOption{zapf}{\def\rntz@font{zapf}}
\DeclareOption{libertine}{\def\rntz@font{libertine}}
\DeclareOption{cm}{\def\rntz@font{cm}}

\DeclareOption{twocolumn}{\ClassWarning{rntz}{Two-column mode is not supported.}}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}

% Defaults
\ExecuteOptions{zapf}
\ProcessOptions\relax

%% ---- Basic layout ----
\LoadClass{extarticle}

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
  {\titlesize\@title\vspace{0.5ex}\par}%
  {\authorsize\@author\vspace{0.5ex}\par}%
  {\authorsize\@date\par}%
  \endgroup\FloatBarrier}

%% ---- Abstracts ----
\renewenvironment{abstract}
  {\vspace{1em}\textbf{Abstract.}}
  {}

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

%% \titlespacing*{\section}{0pt}{\baselineskip}{.5\baselineskip}
%% \titlespacing*{\subsection}{0pt}{\baselineskip}{.5\baselineskip}
%% \titlespacing*{\subsubsection}{0pt}{\baselineskip}{.5\baselineskip}

\titlespacing*{\section}{0pt}{3.5\parsep}{1.75\parsep}
%% \titlespacing*{\section}{0pt}{4\parsep}{2\parsep}
\titlespacing*{\subsection}{0pt}{3\parsep}{1.5\parsep}
\titlespacing*{\subsubsection}{0pt}{3\parsep}{1.5\parsep}

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
%% \renewcommand{\header}{\sffamily\bfseries} % or, in sans-serif
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
