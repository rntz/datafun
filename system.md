\newcommand{\N}{\mathbb{N}}
\newcommand{\x}{\times}
\newcommand{\ms}{\mathsf}
\newcommand{\mono}{\rightsquigarrow}
\newcommand{\ent}{\vdash}
\newcommand{\fn}{\lambda}
\newcommand{\monofn}{\hat{\lambda}}
\newcommand{\binder}{.\,}
\newcommand{\bind}[1]{#1\binder}
\newcommand{\pipe}{\hspace{0.5em}|\hspace{0.5em}}
\newcommand{\FS}{\ms{FS}}
\newcommand{\GD}{\Delta}
\newcommand{\GG}{\Gamma}
\newcommand{\of}{:\!}

\newcommand{\case}[5]{%
\ms{case}~{#1}~\ms{of}~\ms{in}_1\,{#2}\to{#3};\,\ms{in}_2\,{#4}\to{#5}}
\newcommand{\letin}[3]{\ms{let}~{#1}\in{#2}~\ms{in}~{#3}}

# Syntax

$$\begin{array}{lrrl}
\text{types} & A,B
&::=& \N \pipe A \x B \pipe A \to B \pipe M \mono N \pipe \FS\;A \pipe A + B\\
\text{lattice types} & M,N
&::=& \N \pipe M \x N \pipe A \to M \pipe M \mono N \pipe \FS\;A\\
\text{expressions} & e
&::=& x \pipe \fn\bind{x} e \pipe \monofn\bind{x} e \pipe e_1\;e_2\\
&&|\,& (e_1, e_2) \pipe \pi_i\;e\\
&&|\,& \ms{in}_i\; e \pipe \case{e}{x}{e_1}{y}{e_2}\\
&&|\,& \emptyset \pipe e_1 \vee e_2\\
&&|\,& \{e\} \pipe \letin{x}{e_1}{e_2}\\
\text{contexts} & \GD &::=& \cdot \pipe \GD, x \of A \\
\text{monotone ctxts} & \GG &::=& \cdot \pipe \GG, x \of M\\
\text{typing} & J &::=& \GD;\cdot \ent e : A\\
\text{judgment} &&|\,& \GD;\GG \ent e : M
\end{array}$$

# Typing rules
