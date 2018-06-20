\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntztwocolumn}[2018/06/20]
\RequirePackage{etoolbox}       %for \patchcmd

%% No options yet.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ExecuteOptions{}               % defaults
\ProcessOptions\relax

\LoadClass[9pt,twocolumn]{extarticle}

\RequirePackage[a4paper,text={182mm,257mm}]{geometry}
\setlength\columnsep{16pt}

%% TODO: all this is copy-pasted from rntz.cls. Factor it out!

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

%% ---- Links and references ----
\RequirePackage{hyperref,url}
\hypersetup{colorlinks, linkcolor=ACMBlue, citecolor=ACMBlue, urlcolor=ACMBlue, filecolor=ACMBlue}

%% TODO: less garish colors.

%% cleveref must be loaded AFTER hyperref & amsmath, or it errors; and AFTER
%% amsthm and BEFORE we define theorem styles, otherwise (eg) it calls lemmas
%% "Theorem"s.
\RequirePackage{amsmath,amsthm}
% options: capitalise
\usepackage[nameinlink,noabbrev]{cleveref}

%% ---- Theorem styling ----
%% Everything is numbered sequentially with a single counter.
\theoremstyle{definition}
\newtheorem{theorem}{Theorem}
\newtheorem{conjecture}[theorem]{Conjecture}
\newtheorem{lemma}[theorem]{Lemma}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem*{corollary}{Corollary}
\theoremstyle{plain}            %back to default

%% ---- Document title formatting and sizing ----
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
  {\titlesize\@title\vspace{0.5ex}\\}%
  {\authorsize\@author\vspace{0.5ex}\\}%
  {\authorsize\@date}%
  \endgroup\FloatBarrier\par}


%% ---- Section & subsection titles ----
\RequirePackage{titlesec}    % (sub)section header styling
\RequirePackage{fontaxes}    % selecting tabular lining figures

%% titlesec < 2.10.2 has a bug that prevents showing section numbers. This fixes
%% it. Taken from
%% https://tex.stackexchange.com/questions/96090/formatting-subsections-and-chapters-in-tufte-book/96125
\patchcmd{\ttlh@hang}{\parindent\z@}{\parindent\z@\leavevmode}{}{}
\patchcmd{\ttlh@hang}{\noindent}{}{}{}

% Lotsa whitespace.
\def\rntz@secbefore{1.6em plus .8em minus .4em}
\def\rntz@secafter{.8em plus .4em minus .2em}
\titlespacing*{\section}{0pt}{\rntz@secbefore}{\rntz@secafter}
\titlespacing*{\subsection}{0pt}{\rntz@secbefore}{\rntz@secafter}
\titlespacing*{\subsubsection}{0pt}{\rntz@secbefore}{\rntz@secafter}

%% Spacing.
\newcommand{\header}{\rmfamily\bfseries\lnfigures\tbfigures}
%% \renewcommand{\header}{\rmfamily\itshape}  % or, italics
%% \renewcommand{\header}{\sffamily\bfseries} % or, sans-serif

\titleformat{\section}{\secsize\header}{\thesection}{9pt}{}
\titleformat{\subsection}{\subsecsize\header}{\thesubsection}{9pt}{}
\titleformat{\subsubsection}{\subsecsize\header}{}{0pt}{}
