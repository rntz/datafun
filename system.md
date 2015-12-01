<!-- Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod
tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam,
quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo
consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum
dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident,
sunt in culpa qui officia deserunt mollit anim id est laborum. -->

# Language

## Syntax

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
&&|\,& \fix{x}e\\
\text{contexts} & \GD &::=& \cdot \pipe \GD, x \of A \\
\text{monotone ctxts} & \GG &::=& \cdot \pipe \GG, x \of M\\
\text{typing judgment} & J &::=& \J{\GD}{\cdot}{e}{A}\\
&&|\,& \J{\GD}{\GG}{e}{M}
\end{array}$$

## Typing rules

### Structural rules

These rules are technically unnecessary, as they are (ought to be, no proof yet)
admissible.

$$
\infer[\ms{exchange}]{
  \J{\GD_1,\GD_2}{\GG_1,\GG_2}{e}{A}}{\J{\GD_2,\GD_1}{\GG_2,\GG_1}{e}{A}}
\quad
\infer[\ms{weaken}]{\J{\GD,\GD'}{\GG,\GG'}{e}{A}}{\J{\GD}{\GG}{e}{A}}
\quad
\infer[\ms{forget}]{\J{\GD,x\of M}{\GG}{e}{N}}{\J{\GD}{\GG,x\of M}{e}{N}}
$$

### Other rules

$$
\infer[\ms{hyp}]{\J{\GD}{\GG}{x}{A}}{x\of A \in \GD \cup \GG} \qquad
\infer[\fn]{\J{\GD}{\GG}{\fn\bind{x}{e}}{A \to B}}{
  \J{\GD,x\of A}{\GG}{e}{B}} \qquad
\infer[\ms{app}]{\J{\GD}{\GG}{e_1\;e_2}{B}}{
  \J{\GD}{\GG}{e_1}{A \to B} &
  \J{\GD}{\cdot}{e_2}{B}}
$$\ $$
\infer[\monofn]{\J{\GD}{\GG}{\monofn\bind{x}{e}}{M \mono N}}{
  \J{\GD}{\GG,x \of M}{e}{N}} \qquad
\infer[\widehat{\ms{app}}]{\J{\GD}{\GG}{e_1\;e_2}{N}}{
  \J{\GD}{\GG}{e_1}{M \mono N} &
  \J{\GD}{\GG}{e_2}{M}}
$$\ $$
\infer[(,\!)]{\J{\GD}{\GG}{(e_1, e_2)}{A_1 \x A_2}}{\J{\GD}{\GG}{e_i}{A_i}}
\qquad
\infer[\pi_i]{\J{\GD}{\GG}{\pi_i\; e}{A_i}}{\J{\GD}{\GG}{e}{A_1 \x A_2}}
$$\ $$
\infer[\ms{in}_i]{\J{\GD}{\cdot}{\ms{in}_i\;e}{A_1 + A_2}}{
  \J{\GD}{\cdot}{e}{A_i}} \qquad
\infer[\ms{case}]{\J{\GD}{\GG}{\case{e}{x}{e_1}{y}{e_2}}{C}}{
  \J{\GD}{\cdot}{e}{A + B} &
  \J{\GD,x\of A}{\GG}{e_1}{C} &
  \J{\GD,y\of B}{\GG}{e_2}{C}}
$$\ $$
\infer[\emptyset]{\J{\GD}{\GG}{\emptyset}{M}}{} \qquad
\infer[\vee]{\J{\GD}{\GG}{e_1 \vee e_2}{M}}{\J{\GD}{\GG}{e_i}{M}}
$$\ $$
\infer[\{\}]{\J{\GD}{\GG}{\{e\}}{\FS\;A}}{\J{\GD}{\cdot}{e}{A}} \qquad
\infer[\ms{let}_{\in}]{\J{\GD}{\GG}{\letin{x}{e_1}{e_2}}{M}}{
  \J{\GD}{\GG}{e_1}{\FS\;A} &
  \J{\GD,x\of A}{\GG}{e_2}{M}}
$$\ $$
\infer[\ms{fix}]{\J{\GD}{\GG}{\fix{x}e}{M}}{
  \J{\GD}{\GG,x\of M}{e}{M}}
$$

The \ms{fix} rule is overly permissive in allowing fix-points to be taken at any
lattice type; it needs to be be restricted to some computationally tractable
class of lattice types.

# Proofs

## Admissibility of {\ms{exchange},\ms{weaken},\ms{forget}}

TODO

## Syntactic substitution

Note that whenever two variables are given distinct names $x, y$ it is assumed
$x \ne y$ unless mentioned otherwise.

We could choose to define two substitution operators, one for unrestricted
substitution and the other for monotone substitution, but they coincide on
properly-typed arguments (see substitution theorems below for what I mean by
properly-typed arguments), so we don't bother.

We define substitution $\sub{e_1/x} e_2$, by induction on $e_2$:

$$
\begin{array}{rcl}
  \sub{e/x} x &=& e\\
  \sub{e/x} y &=& y\\
  \sub{e/x}(\fn\bind{y} e') &=& \fn\bind{y} \sub{e/x} e'\\
  \sub{e/x}(\monofn\bind{y} e') &=& \monofn\bind{y} \sub{e/x} e'\\
  \sub{e/x}(e_1\;e_2) &=& (\sub{e/x} e_1)\;(\sub{e/x}e_2)\\
  \sub{e/x}(e_1, e_2) &=& (\sub{e/x}e_1, \sub{e/x}e_2)\\
  \sub{e/x}(\pi_i\; e') &=& \pi_i\;(\sub{e/x} e')\\
  \sub{e/x}(\ms{in}_i\;e') &=& \ms{in}_i\;(\sub{e/x}e')\\
  \sub{e/x}(\case{e'}{y}{e_1}{z}{e_2})
  &=& \case{\sub{e/x} e'}{y}{\sub{e/x}e_1}{z}{\sub{e/x}e_2}\\
  \sub{e/x} \emptyset &=& \emptyset\\
  \sub{e/x}(e_1 \vee e_2) &=& (\sub{e/x}e_1) \vee (\sub{e/x} e_2)\\
  \sub{e/x}\{e'\} &=& \{\sub{e/x}e'\}\\
  \sub{e/x}(\letin{y}{e_1}{e_2}) &=& \letin{y}{\sub{e/x}e_1}{\sub{e/x}e_2}\\
  \sub{e/x}(\fix{y} e') &=& \fix{y} \sub{e/x} e'
\end{array}
$$

<!-- TODO: theorem numbering. what package provides \begin{theorem} again? -->

\textbf{Theorem 1.1, substitution for unrestricted variables:} If
$\J{\GD}{\cdot}{e}{A}$ and $\J{\GD,x\of A}{\GG}{e'}{B}$ then
$\J{\GD}{\GG}{\sub{e/x}{e'}}{B}$.

\textbf{Proof:} By induction on $\J{\GD,x\of A}{\GG}{e'}{B}$, assuming in each
case that $\J{\GD}{\cdot}{e}{A}$:

\begin{quote}
  \begin{description}
  %% \item[Case \(\infer{\J{\GD,x\of A}{\GG}{x}{A}}{x\of A \in \GD\cup\GG}\):]
  %%   By assumption, $\J{\GD}{\GG}{e}{A}$
  \item[Case \ms{hyp}, $x \ne y$:] Given \[
    \infer[\ms{hyp}]{\J{\GD,x\of A}{\GG}{y}{B}}{
      y\of B \in (\GD,x\of A)\cup\GG}
    \]

    Since $x \ne y$, evidently $y \of B \in \GD \cup \GG$, thus:
    \[\infer[\ms{hyp}]{\J{\GD}{\GG}{y}{B}}{y\of B \in \GD\cup\GG}\]

  \item[Case \ms{hyp}, $x = y$:] Given \[
    \infer[\ms{hyp}]{\J{\GD,x\of A}{\GG}{x}{A}}{
      x\of A \in (\GD,x\of A)\cup\GG}\]

    By weakening our assumption we have $\J{\GD}{\GG}{e}{A}$, which suffices.

  \item[Case $\fn$]: Given \[
    \infer[\fn]{\J{\GD,x\of A}{\GG}{\fn\bind{y} e'}{B \to C}}{
      \J{\GD,x\of A,y\of B}{\GG}{e'}{C}}
    \]

    By our IH, exchange, and weakening, we have $\J{\GD,y :
      B}{\GG}{\sub{e/x}e'}{C}$. Thus:
    \[
    \infer{\J{\GD}{\GG}{\fn\bind{y} \sub{e/x} e'}{B \to C}}{
      \J{\GD,y : B}{\GG}{\sub{e/x}e'}{C}}
    \]

  \item[Case $\monofn$]: Given \[
    \infer[\monofn]{\J{\GD,x\of A}{\GG}{\monofn\bind{y} e'}{M \mono N}}{
      \J{\GD,x\of A}{\GG,y \of M}{e'}{N}}
    \]

    By our IH, we have $\J{\GD}{\GG,y \of M}{\sub{e/x}e'}{N}$. Thus:
    \[
    \infer[\monofn]{\J{\GD}{\GG}{\monofn\bind{y} \sub{e/x}e'}{M \mono N}}{
      \J{\GD}{\GG,y\of M}{\sub{e/x} e'}{N}
      }
    \]

  \item[Case $\ms{app}$:] Given \[
    \infer[\ms{app}]{\J{\GD,x\of A}{\GG}{e_1\;e_2}{C}}{
      \J{\GD,x\of A}{\GG}{e_1}{B \to C} &
      \J{\GD,x\of A}{\cdot}{e_2}{B}}
    \]

    By our IHs, we have $\J{\GD}{\GG}{\sub{e/x} e_1}{B\to C}$ and
    $\J{\GD}{\cdot}{\sub{e/x}e_2}{B}$. Thus: \[
    \infer[\ms{app}]{\J{\GD}{\GG}{(\sub{e/x} e_1)\;(\sub{e/x} e_2)}{C}}{
        \J{\GD}{\GG}{\sub{e/x} e_1}{B \to C} &
        \J{\GD}{\cdot}{\sub{e/x} e_2}{B}}
    \]

  \item[Case $\widehat{\ms{app}}$:] Given \[
    \infer[\widehat{\ms{app}}]{\J{\GD,x\of A}{\GG}{e_1\;e_2}{N}}{
      \J{\GD,x\of A}{\GG}{e_1}{M \mono N} &
      \J{\GD,x\of A}{\GG}{e_2}{N}}
    \]

    By our IHs, we have $\J{\GD}{\GG}{\sub{e/x} e_1}{M\to N}$ and
    $\J{\GD}{\GG}{\sub{e/x}e_2}{M}$. Thus: \[
    \infer[\widehat{\ms{app}}]{
      \J{\GD}{\GG}{(\sub{e/x} e_1)\;(\sub{e/x} e_2)}{N}
    }{
        \J{\GD}{\GG}{\sub{e/x} e_1}{M \mono N} &
        \J{\GD}{\GG}{\sub{e/x} e_2}{M}}
    \]

  \item[Case \ms{case}:] {\color{red} TODO}

  \item[Case $\{\}$:] Given \[
    \infer[\{\}]{\J{\GD,x\of A}{\GG}{\{e'\}}{\FS\;B}}{
      \J{\GD,x\of A}{\cdot}{e'}{B}}
    \]

    By IH we have $\J{\GD}{\cdot}{\sub{e/x} e'}{B}$, thus:\[
    \infer[\{\}]{\J{\GD}{\GG}{\{\sub{e/x} e'\}}{\FS\;B}}{
      \J{\GD}{\cdot}{\sub{e/x} e'}{B}}
    \]

  \item[Case $\ms{let}_{\in}$:] Given \[
    \infer[\ms{let}_{\in}]{\J{\GD,x\of A}{\GG}{\letin{y}{e_1}{e_2}}{M}}{
      \J{\GD,x\of A}{\GG}{e_1}{\FS\;B} &
      \J{\GD,x\of A,y\of B}{\GG}{e_2}{M}}\]

    By our IHs, exchange, and weakening, we have
    $\J{\GD}{\GG}{\sub{e/x}e_1}{\FS\;B}$ and $\J{\GD,y\of B}{\GG}{\sub{e/x}
      e_2}{M}$. Thus:
    \[
    \infer[\ms{let}_{\in}]{
      \J{\GD}{\GG}{\letin{y}{\sub{e/x}e_1}{\sub{e/x}e_2}}{M}
    }{
      \J{\GD}{\GG}{\sub{e/x} e_1}{\FS\;B} &
      \J{\GD,y\of B}{\GG}{\sub{e/x} e_2}{M}
    }
    \]

  \item[Case $\ms{fix}$:] Given \[
    \infer[\ms{fix}]{\J{\GD,x\of A}{\GG}{\fix{y} e'}{M}}{
      \J{\GD,x\of A}{\GG,y \of M}{e'}{M}}
    \]

    By our IH we have $\J{\GD}{\GG,y\of M}{\sub{e/x} e'}{M}$. Thus: \[
    \infer[\ms{fix}]{\J{\GD}{\GG}{\fix{y} \sub{e/x} e'}{M}}{
      \J{\GD}{\GG,y\of M}{\sub{e/x} e'}{M}
    }\]

  \item[Omitted cases:] $(,\!)$, $\pi_i$, $\ms{in}_i$, $\emptyset$, and
    ${\vee}$ are trivial.

  \end{description}
\end{quote}

\textbf{Theorem 1.2, substitution for monotone variables:} If
$\J{\GD}{\GG}{e}{M}$ and $\J{\GD}{\GG,x \of M}{e'}{N}$ then
$\J{\GD}{\GG}{\sub{e/x}{e'}}{N}$.

\textbf{Proof:} By induction on $\J{\GD}{\GG,x \of M}{e'}{N}$, assuming
$\J{\GD}{\GG}{e}{M}$ in each case:

\begin{quote}
  \begin{description}
  \item[Case \ms{hyp}, $x \ne y$:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{y}{N}}{y\of N \in \GD\cup(\GG,x\of M)}
    \]

    Since $x \ne y$, evidently $y\of N \in \GD \cup \GG$. Thus:\[
    \infer{\J{\GD}{\GG}{y}{N}}{y\of N \in \GD\cup\GG}
    \]

  \item[Case \ms{hyp}, $x = y$:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{x}{M}}{x\of M \in \GD\cup\GG}
    \]

    By assumption, $\J{\GD}{\GG}{e}{M}$, which suffices.

  \item[Case $\fn$]: Given \[
    \infer{\J{\GD}{\GG,x\of M}{\fn\bind{y}{e'}}{A \to N}}{
      \J{\GD,y\of A}{\GG,x\of M}{e'}{N}}\]

    By our IH and weakening, $\J{\GD,y:A}{\GG}{\sub{e/x} e'}{N}$. Thus: \[
    \infer{\J{\GD}{\GG}{\fn\bind{y} \sub{e/x} e'}{A \to N}}{
      \J{\GD,y\of A}{\GG}{\sub{e/x} e'}{N}}
    \]

  \item[Case $\monofn$]: Given
  \item[Case $\ms{app}$:] Given
  \item[Case $\widehat{\ms{app}}$:] Given
  \item[Case \ms{case}:] {\color{red} TODO}
  \item[Case $\{\}$:] Given 
  \item[Case $\ms{let}_{\in}$:] Given 
  \item[Case $\ms{fix}$:] Given 
  \item[Omitted cases:] $(,\!)$, $\pi_i$, $\ms{in}_i$, $\emptyset$, and ${\vee}$
    are trivial.
  \end{description}
\end{quote}
