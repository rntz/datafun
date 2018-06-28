\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntztwocolumn}[2018/06/20]
\RequirePackage{etoolbox}       %for \patchcmd

%% No options yet.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ExecuteOptions{}               % defaults
\ProcessOptions\relax

\LoadClass[9pt,twocolumn]{extarticle}
\RequirePackage[a4paper,text={182mm,257mm}]{geometry}
\setlength\parskip{0pt}
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

%% Section title & paragraph spacing
\def\secbefore{1\baselineskip plus .4\baselineskip minus .2\baselineskip}
\def\secafter{.4\baselineskip plus .16\baselineskip minus .08\baselineskip}
\def\subsecbefore{.8\baselineskip plus .32\baselineskip minus .16\baselineskip}
\def\subsecafter{.32\baselineskip plus .128\baselineskip minus .064\baselineskip}
\titlespacing*{\section}{0pt}{\secbefore}{\secafter}
\titlespacing*{\subsection}{0pt}{\secbefore}{\secafter}
\titlespacing*{\subsubsection}{0pt}{\subsecbefore}{\subsecafter}
\titlespacing*{\paragraph}{0pt}{\subsecbefore}{1.2em}

% 0.5 plus 0.2 minus 0.1

%% Section title sizing
\newcommand{\secsize}{\Large}
\newcommand{\subsecsize}{\large}
\newcommand{\subsubsecsize}{\normalsize}
\newcommand{\header}{\rmfamily\bfseries\lnfigures\tbfigures}
%% \renewcommand{\header}{\rmfamily\itshape}  % or, italics
%% \renewcommand{\header}{\sffamily\bfseries} % or, sans-serif

\titleformat{\section}{\secsize\header}{\thesection}{1em}{}
\titleformat{\subsection}{\subsecsize\header}{\thesubsection}{1em}{}
\titleformat{\subsubsection}{\subsubsecsize\header}{}{0pt}{}
\titleformat*{\paragraph}{\bfseries}{}
