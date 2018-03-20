\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntznotes}[2018/03/19]

\LoadClass{article}
\RequirePackage[a5paper,margin=1cm,bottom=1.75cm]{geometry}

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

%% ---- Paragraph & list styling ----
\RequirePackage{enumitem}
\setlength{\parindent}{1.0pc}
\setlist{noitemsep,topsep=\smallskipamount}

%% ---- Hyperlinks ----
\RequirePackage{hyperref,url}
\hypersetup{colorlinks,linkcolor=ACMRed,citecolor=ACMPurple,urlcolor=ACMDarkBlue,filecolor=ACMDarkBlue}

%% ---- Fonts ---
\RequirePackage[osf]{libertine}
\linespread{1.05}
\RequirePackage[libertine]{newtxmath}

%% ---- Section & subsection titles ----
\RequirePackage{textcase,titlesec}
%% titlesec < 2.10.2 has a bug that prevents showing section numbers. This fixes
%% it. Taken from
%% https://tex.stackexchange.com/questions/96090/formatting-subsections-and-chapters-in-tufte-book/96125
\RequirePackage{etoolbox}
\makeatletter
\patchcmd{\ttlh@hang}{\parindent\z@}{\parindent\z@\leavevmode}{}{}
\patchcmd{\ttlh@hang}{\noindent}{}{}{}
\makeatother

%% Spacing.
\newcommand{\hnopre}{\hspace*{2mm}}
\newcommand{\hnopost}{\hspace*{.5mm}}
\newcommand{\header}{\itshape\rmfamily}
\newcommand{\hno}[1]{\colorhno{white}{black}{#1}}
\newcommand{\colorhno}[3]%
{\llap{\colorbox{#1}{\parbox{1cm}{\hfill{\color{#2}#3\hnopost}}}\hnopre}}

%% Uncomment for colorless header numbers.
\renewcommand{\colorhno}[3]{%
{\llap{\colorbox{white}{\parbox{1cm}{\hfill{#3\hnopost}}\hnopre}}}}

\titlespacing*{\section}{0pt}{1.25em}{.5em}
\titlespacing*{\subsection}{0pt}{1.25em}{.5em}

\titleformat{\section}{\large\header}
            {\colorhno{cyan}{white}{\thesection}}{0pt}{}
\titleformat{\subsection}{\normalsize\header}
            {\colorhno{ACMOrange}{white}{\thesubsection}}{0pt}{}
%% Uncomment for colorless subsection headers.
%% \titleformat{\subsection}{\normalsize\header}{\hno{\thesubsection}}{0pt}{}


%% %% OUTDATED: Mathpazo sections
%% \usepackage{mathpazo}
%% \linespread{1.15}

%% %% Spacing.
%% \titlespacing*{\section}{0pt}{\baselineskip}{0.5\baselineskip}
%% \titlespacing*{\subsection}{0pt}{\baselineskip}{0.5\baselineskip}

%% \titleformat{\section}%
%%   {\large\itshape\rmfamily}% format applied to label+text
%%   {\llap{\parbox{1cm}{\hfill\thesection}\hspace*{0.3cm}}}% label
%%   {0pt}% horizontal separation between label and title body
%%   {}% before the title body
%%   []% after the title body

%% \titleformat{\subsection}
%%   {\normalsize\itshape\rmfamily}
%%   {\llap{\parbox{1cm}{\hfill\thesubsection}\hspace*{0.3cm}}}
%%   {0pt}
%%   {}
