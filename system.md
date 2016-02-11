# Language

## Syntax

$$\begin{array}{lrrl}
\text{types} & A,B
&::=& \bool \pipe \N \pipe A \x B \pipe A + B \pipe A \to B
\pipe A \mono B \pipe \FS\;A\\
\text{lattice types} & L,M
&::=& \bool \pipe \N \pipe L \x M \pipe A \to L \pipe A \mono L \pipe \FS\;A\\
\text{finite types} & F,G
&::=& F \x G \pipe F + G \pipe F \to G \pipe F \mono G \pipe \FS\;F\\
\text{expressions} & e
&::=& x \pipe \fn\bind{x} e \pipe e_1\;e_2
\pipe (e_1, e_2) \pipe \pi_i\;e \\
&&|\,& \ms{in}_i\;e \pipe \case{e}{x}{e_1}{y}{e_2}\\
&&|\,& \emptyset \pipe e_1 \vee e_2 \pipe \{e\} \pipe \letin{x}{e_1}{e_2}\\
&&|\,& \fix{x}e\\
\text{contexts} & \GD,\GG &::=& \cdot \pipe \GD, x \of A \\
\text{typing judgment} & J &::=& \J{\GD}{\GG}{e}{A}
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
$$

As originally formulated, there was an additional structural rule, \ms{forget}:
$$
\infer[\ms{forget}]{\J{\GD,x\of A}{\GG}{e}{B}}{\J{\GD}{\GG,x\of A}{e}{B}}
$$

However, \ms{forget} is not used in any proofs, and is moreover derivable, as a
form of $\beta$-expansion, from weakening and the rules for monotone functions
(with a bit of term elaboration):
$$
\infer[\ms{app}^+]{\J{\GD,x\of A}{\GG}{(\fn\bind{x} e)\; x}{B}}{
  \infer[\ms{weaken}]{\J{\GD,x\of A}{\GG}{\fn\bind{x}e}{A \mono B}}{
    \infer[\fn^+]{\J{\GD}{\GG}{\fn\bind{x}e}{A \mono B}}{
      \J{\GD}{\GG,x\of A}{e}{B}}} &
  \infer[\ms{hyp}]{\J{\GD,x\of A}{\GG}{x}{A}}{}
  }
$$

### Other rules

$$
\infer[\ms{hyp}]{\J{\GD}{\GG}{x}{A}}{x\of A \in \GD \cup \GG} \qquad
\infer[\fn]{\J{\GD}{\GG}{\fn\bind{x}{e}}{A \to B}}{
  \J{\GD,x\of A}{\GG}{e}{B}} \qquad
\infer[\fn^+]{\J{\GD}{\GG}{\fn\bind{x}{e}}{A \mono B}}{
  \J{\GD}{\GG,x \of A}{e}{B}}
$$\ $$
\infer[\ms{app}]{\J{\GD}{\GG}{e_1\;e_2}{B}}{
  \J{\GD}{\GG}{e_1}{A \to B} &
  \J{\GD}{\cdot}{e_2}{B}} \qquad
\infer[\ms{app}^+]{\J{\GD}{\GG}{e_1\;e_2}{B}}{
  \J{\GD}{\GG}{e_1}{A \mono B} &
  \J{\GD}{\GG}{e_2}{A}}
$$\ $$
\infer[(,\!)]{\J{\GD}{\GG}{(e_1, e_2)}{A_1 \x A_2}}{\J{\GD}{\GG}{e_i}{A_i}}
\qquad
\infer[\pi_i]{\J{\GD}{\GG}{\pi_i\; e}{A_i}}{\J{\GD}{\GG}{e}{A_1 \x A_2}}
\qquad
\infer[\ms{in}_i]{\J{\GD}{\GG}{\ms{in}_i\;e}{A_1 + A_2}}{
  \J{\GD}{\GG}{e}{A_i}}
$$\ $$
\infer[\ms{case}]{\J{\GD}{\GG}{\case{e}{x_1}{e_1}{x_2}{e_2}}{C}}{
  \J{\GD}{\cdot}{e}{A_1 + A_2} &
  \J{\GD,x_i\of A_i}{\GG}{e_i}{C}
}
$$\ $$
\infer[\ms{case}^+]{\J{\GD}{\GG}{\case{e}{x_1}{e_1}{x_2}{e_2}}{C}}{
  \J{\GD}{\GG}{e}{A_1 + A_2} &
  \J{\GD}{\GG, x_i \of A_i}{e_i}{C}
}
$$\ $$
\infer[\emptyset]{\J{\GD}{\GG}{\emptyset}{M}}{} \qquad
\infer[\vee]{\J{\GD}{\GG}{e_1 \vee e_2}{M}}{\J{\GD}{\GG}{e_i}{M}} \qquad
\infer[\{\}]{\J{\GD}{\GG}{\{e\}}{\FS\;A}}{\J{\GD}{\cdot}{e}{A}}
$$\ $$
\infer[\bigvee_\in]{\J{\GD}{\GG}{\letin{x}{e_1}{e_2}}{M}}{
  \J{\GD}{\GG}{e_1}{\FS\;A} &
  \J{\GD,x\of A}{\GG}{e_2}{M}}
$$\ $$
\infer[\ms{fix}]{\J{\GD}{\GG}{\fix{x}e}{M}}{
  \J{\GD}{\GG,x\of M}{e}{M} & M~\ms{finite} & M~\ms{equality}}
$$

The restriction of the \ms{fix} rule to finite lattices is necessary to avoid
nontermination.

<!--
The \ms{fix} rule is overly permissive in allowing fix-points to be taken at any
lattice type; it needs to be be restricted to some computationally tractable
class of lattice types.
-->



# Denotational semantics

A unital semilattice (usl) is a poset $\pair{A}{\le}$ in which every finite
subset $X \subseteq_{\ms{fin}} A$ has a least upper bound, written $\bigvee X$.
We define $\unit$ and $\vee$ with respect to an arbitrary usl as follows:
$$\begin{array}{rcl}
  \unit &=& \bigvee \emptyset\\
  a \vee b &=& \bigvee \{a,b\}
\end{array}$$

We consider only usls in which $\bigvee$, and thus $\unit$ and $\vee$, are
computable. However, equality $=$ and thus ordering $\le$ may not always be
decidable. (Equality and ordering are interdefinable given $\vee$, since $(a
\le b) \iff (a \vee b = b)$.)

<!-- Let \ms{Set} be the category of sets and functions and \ms{Poset} be the
category of posets and monotone functions. -->

Given posets $A,B$ we use the following notation:
\begin{center}\begin{tabular}{cl}
    \one & one-element poset, $\{\triv\}$, $\triv \le \triv$\\
    $A + B$ & disjointly-ordered poset on disjoint union of $A$ and $B$\\
    $A \x B$ & pointwise poset on pairs of $A$s and $B$s\\
    $A \to B$ & poset of functions from $A$ to $B$, ordered pointwise\\
    $A \mono B$
    & poset of monotone functions from $A$ to $B$, ordered pointwise\\
    $\FS\;A$ & usl of finite subsets of $A$ ordered by inclusion\\
\end{tabular}\end{center}

Note that $A \x B$ is an usl if $A$ and $B$ are, that $A \to B$ and $A \mono B$
are usls if $B$ is, and $\FS\;A$ is always an usl (indeed, is the free usl on
the underlying set of $A$). $A + B$ is an usl when exactly one of $A$ or $B$ is
empty and the other is an usl, as otherwise it has no least element.

## Semantics of types and contexts

Types are interpreted as posets:
$$\begin{array}{lcl}
  \den{\N} &=& \pair{\N}{\le}\\
  \den{A + B} &=& \den{A} + \den{B}\\
  \den{A \x B} &=& \den{A} \x \den{B}\\
  \den{A \to B} &=& \den{A} \to \den{B}\\
  \den{A \mono B} &=& \den{A} \mono \den{B}\\
  \den{\FS\;A} &=& \FS\;\den{A}\\
\end{array}$$

We extend this to contexts:
$$\begin{array}{lcl}
  \den{\cdot} &=& \one\\
  \den{\GD,x\of A} &=& \den{\GD} \x \den{A}\\
\end{array}$$

As a lemma, we show that for ``lattice types'' $M$, $\den{M}$ is an usl with a
computable $\bigvee$ (and thus computable $\unit$ and $\vee$). \omitted{TODO:
  prove lemma}

## Semantics of type derivations

\newcommand{\fux}[2]{\Den{\vcenter{\infer{#1}{#2}}}}
\newcommand{\dg}{\;\delta\;\gamma}

We define a semantics on type derivations $J$ with the following signature:
$$\begin{array}{lcl}
  \den{\J{\GD}{\GG}{e}{A}} &\in& \den{\GD} \to \den{\GG} \mono \den{A}
\end{array}$$

$$
\begin{array}{rcll}
  \textbf{Derivation} && \textbf{Denotes}
  & \textbf{Monotone in }\gamma
  \vspace{.4em}\\
  \fux{\J{x_1\of A_1, ..., x_n\of A_N}{\GG}{x_i}{A_i}}{\phantom{.}}\dg
  &=& \pi_i\;\delta & \text{constant in }\gamma
  \vspace{.8em}\\
  \fux{\J{\GD}{x_1\of M_1, ..., x_n\of M_n}{x_i}{M_i}}{\phantom{.}}\dg
  &=& \pi_i\;\gamma & \pi_i\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\emptyset}{M}}{\phantom{.}}\dg
  %% \den{\emptyset : M}\dg
  &=& \unit & \text{constant in }\gamma
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{e_1 \vee e_2}{M}}{
    \J{\GD}{\GG}{e_1}{M} &
    \J{\GD}{\GG}{e_2}{M}}\dg
  %% \den{e_1 \vee e_2 : M}\dg
  &=& \den{e_1}\dg \vee \den{e_2}\dg
  & \text{$\vee$ monotone, IHs}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\{e\}}{\FS\;A}}{\J{\GD}{\cdot}{e}{A}}\dg
  &=& \{\den{e}\;\delta\;\triv\} & \text{constant in }\gamma
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\letin{x}{e_1}{e_2}}{M}}{
    \J{\GD}{\GG}{e_1}{\FS\;A} &
    \J{\GD,x\of A}{\GG}{e_2}{M}}\dg
  &=& \displaystyle\bigvee_{x \,\in\, \den{e_1}\,\delta\,\gamma}
  \den{e_2}\;\tuple{\delta,x}\;\gamma
  & \text{\omitted{TODO}}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\fn\bind{x} e}{A \to B}}{
    \J{\GD,x\of A}{\GG}{e}{B}}\dg
  &=& x \mapsto \den{e}\;\tuple{\delta,x}\;\gamma
  & \den{e}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\fn\bind{x} e}{A \mono B}}{
    \J{\GD}{\GG,x\of A}{e}{B}}\dg
  &=& x \mapsto \den{e} \;\delta \;\tuple{\gamma,x}
  & \den{e}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{e_1\;e_2}{B}}{
    \J{\GD}{\GG}{e_1}{A \to B} &
    \J{\GD}{\cdot}{e_2}{A}} \dg
  &=& \den{e_1}\dg\;(\den{e_2}\;\delta\;\triv)
  & \text{\omitted{TODO}}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{e_1\;e_2}{B}}{
    \J{\GD}{\GG}{e_1}{A \mono B} &
    \J{\GD}{\GG}{e_2}{B}} \dg
  &=& \den{e_1}\dg\;(\den{e_2}\dg)
  & \den{e_i}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\ms{in}_i\;e}{A_1 + A_2}}{
    \J{\GD}{\GG}{e}{A_i}}\dg
  &=& \ms{in}_i\;(\den{e}\dg)
  & \ms{in}_i, \den{e}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\case{e}{x_1}{e_1}{x_2}{e_2}}{B}}{
    \J{\GD}{\cdot}{e}{A_1 + A_2} &
    \J{\GD,x_i\of A_i}{\GG}{e_i}{B}}
  \dg
  &=&
  \begin{cases}
    \den{e_1}\;\pair{\delta}{x}\;\gamma
    &\text{if }\den{e_2}\;\delta\;\triv = \ms{in}_1\;x\\
    \den{e_2}\;\pair{\delta}{x}\;\gamma
    &\text{if }\den{e_2}\;\delta\;\triv = \ms{in}_2\;x\\
  \end{cases}
  & \den{e_i}\text{ monotone}
  \vspace{.8em}\\
  %% TODO: denotation of monotone \case
  \fux{\J{\GD}{\GG}{\case{e}{x_1}{e_1}{x_2}{e_2}}{B}}{
    \J{\GD}{\GG}{e}{A_1 + A_2} &
    \J{\GD}{\GG,x_i\of A_i}{e_i}{B}
  }\dg
  &=& \text{\omitted{TODO}}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{(e_1, e_2)}{A_1 \x A_2}}{
    \J{\GD}{\GG}{e_i}{A_i}}\dg
  &=& \pair{\den{e_1}\dg}{\den{e_2}\dg} & \den{e_i}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\pi_i\;e}{A_i}}{
    \J{\GD}{\GG}{e}{A_1 + A_2}}\dg
  &=& \pi_i\;(\den{e}\dg) & \pi_i,\,\den{e}\text{ monotone}
  \vspace{.8em}\\
  \fux{\J{\GD}{\GG}{\fix{x}e}{M}}{
    \J{\GD}{\GG,x\of M}{e}{M} &
    M~\ms{finite} &
    M~\ms{equality}
  }\dg
  &=& \ms{fix}_{\den{M}}\;(\fn\bind{x} \den{e}\;\pair{\delta}{x}\;\gamma)
  & \text{\omitted{TODO}}
\end{array}
$$

Note that the denotation of $\fix{x} e$ being well-defined relies on the
following lemma:

\textbf{Lemma:} The denotation $\den{M}$ of a \emph{finite} lattice type $M$ is
a finite usl. \textbf{Proof:} \omitted{Omitted}.

From this it follows immediately (\omitted{TODO: reference some proof of this
  well-known fact}) that it is a complete join-semilattice, and therefore a
complete lattice, and therefore has a least fix-point (by Knaster-Tarski).



# Proofs

## Admissibility of {\ms{exchange},\ms{weaken}}

\textcolor{red}{TODO}

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

\textbf{Lemma, useless substitution:} If $\J{\GD}{\GG}{e}{A}$ and $x \not\in
\GD\cup\GG$, then $\sub{e'/x}e = e$. \textbf{Proof:} \omitted{Omitted}.

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

  \item[Case $\fn^+$]: Given \[
    \infer[\fn^+]{\J{\GD,x\of A}{\GG}{\fn\bind{y} e'}{M \mono N}}{
      \J{\GD,x\of A}{\GG,y \of M}{e'}{N}}
    \]

    By our IH, we have $\J{\GD}{\GG,y \of M}{\sub{e/x}e'}{N}$. Thus:
    \[
    \infer[\fn^+]{\J{\GD}{\GG}{\fn\bind{y} \sub{e/x}e'}{M \mono N}}{
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

  \item[Case $\ms{app}^+$:] Given \[
    \infer[\ms{app}^+]{\J{\GD,x\of A}{\GG}{e_1\;e_2}{N}}{
      \J{\GD,x\of A}{\GG}{e_1}{M \mono N} &
      \J{\GD,x\of A}{\GG}{e_2}{N}}
    \]

    By our IHs, we have $\J{\GD}{\GG}{\sub{e/x} e_1}{M\to N}$ and
    $\J{\GD}{\GG}{\sub{e/x}e_2}{M}$. Thus: \[
    \infer[\ms{app}^+]{
      \J{\GD}{\GG}{(\sub{e/x} e_1)\;(\sub{e/x} e_2)}{N}
    }{
        \J{\GD}{\GG}{\sub{e/x} e_1}{M \mono N} &
        \J{\GD}{\GG}{\sub{e/x} e_2}{M}}
    \]

  \item[Case \ms{case}:] Given \[
    \infer{
      \J{\GD,x\of A}{\GG}{\case{e'}{y}{e_1}{z}{e_2}}{D}
    }{
      \J{\GD,x\of A}{\cdot}{e'}{B + C} &
      \J{\GD,x\of A,y\of B}{\GG}{e_1}{D} &
      \J{\GD,x\of A,z\of C}{\GG}{e_2}{D}
    }
    \]

    By our IHs, exchange, and weakening, we have:
    \begin{itemize}
    \item $\J{\GD}{\cdot}{\sub{e/x} e'}{B + C}$,
    \item $\J{\GD,y\of B}{\GG}{\sub{e/x}e_1}{D}$, and
    \item $\J{\GD,z \of C}{\GG}{\sub{e/x} e_2}{D}$.
    \end{itemize}
    Thus:
    \[
    \infer{
      \J{\GD}{\GG}{\case{\sub{e/x}e'}{y}{\sub{e/x}e_1}{z}{\sub{e/x}e_2}}{D}
    }{
      \J{\GD}{\cdot}{\sub{e/x}e'}{B + C} &
      \J{\GD,y\of B}{\GG}{\sub{e/x}e_1}{D} &
      \J{\GD,z\of C}{\GG}{\sub{e/x}e_2}{D}
    }
    \]

  \item[Case $\ms{case}^+$:] \omitted{TODO}

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

  \item[\omitted{Omitted cases:}] $(,\!)$, $\pi_i$, $\ms{in}_i$,
    $\emptyset$, and ${\vee}$ are trivial.

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

  \item[Case $\fn^+$]: Given \[
    \infer{\J{\GD}{\GG,x \of M}{\fn\bind{y} e'}{N \mono O}}{
      \J{\GD}{\GG,x \of M, y \of N}{e'}{O}}
    \]

    By our IH, exchange, and weakening, we have $\J{\GD}{\GG,y\of N}{\sub{e/x}
      e'}{O}$. Thus:
    \[
    \infer{\J{\GD}{\GG}{\fn\bind{y} \sub{e/x} e'}{N \mono O}}{
      \J{\GD}{\GG,y\of N}{\sub{e/x} e'}{O}}
    \]

  \item[Case $\ms{app}$:] Given \[
    \infer{\J{\GD}{\GG,x \of M}{e_1\;e_2}{N}}{
      \J{\GD}{\GG,x\of M}{e_1}{A \to N} &
      \J{\GD}{\cdot}{e_2}{A}}
    \]

    By our IH we have $\J{\GD}{\GG}{\sub{e/x} e_1}{A \to N}$. Since $x$ does not
    occur free in $e_2$, $\sub{e/x} e_2 = e_2$. Thus, this suffices:
    \[
    \infer{\J{\GD}{\GG}{(\sub{e/x} e_1)\;e_2}{N}}{
      \J{\GD}{\GG}{\sub{e/x} e_1}{A \to N} &
      \J{\GD}{\cdot}{e_2}{A}}
    \]

  \item[Case $\ms{app}^+$:] Given \[
    \infer{\J{\GD}{\GG,x \of M}{e_1\;e_2}{O}}{
      \J{\GD}{\GG,x \of M}{e_1}{N \mono O} &
      \J{\GD}{\GG,x \of M}{e_2}{N}}
    \]

    By our IHs, we have $\J{\GD}{\GG}{\sub{e/x}e_1}{N \mono O}$ and
    $\J{\GD}{\GG}{\sub{e/x}e_2}{N}$. Thus:
    \[
    \infer{\J{\GD}{\GG}{(\sub{e/x} e_1)\;(\sub{e/x} e_2)}{O}}{
      \J{\GD}{\GG}{\sub{e/x} e_1}{N \mono O} &
      \J{\GD}{\GG}{\sub{e/x} e_2}{N}}
    \]

  \item[Case \ms{case}:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{\case{e'}{y}{e_1}{z}{e_2}}{N}}{
      \J{\GD}{\cdot}{e'}{A + B} &
      \J{\GD,y \of A}{\GG,x\of M}{e_1}{N} &
      \J{\GD,z \of B}{\GG,x\of M}{e_2}{N}}
    \]

    Since $x$ does not occur free in $e'$, $\sub{e/x}e' = e'$. By our IHs and
    weakening, we have $\J{\GD,y\of A}{\GG}{\sub{e/x} e_1}{N}$ and $\J{\GD,z\of
      B}{\GG}{\sub{e/x}e_2}{N}$. Thus, this suffices:
    \[
    \infer{\J{\GD}{\GG}{\case{e'}{y}{\sub{e/x}e_1}{z}{\sub{e/x}e_2}}{N}}{
      \J{\GD}{\cdot}{e'}{A+B} &
      \J{\GD,y\of A}{\GG}{\sub{e/x} e_1}{N} &
      \J{\GD,z\of B}{\GG}{\sub{e/x} e_2}{N}}
    \]

  \item[Case $\ms{case}^+$:] \omitted{TODO}

  \item[Case $\{\}$:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{\{e'\}}{\FS\;A}}{
      \J{\GD}{\cdot}{e'}{A}}
    \]

    Since $x$ does not occur free in $e'$, $\sub{e/x} e' = e'$. Thus, this
    suffices:
    \[
    \infer{\J{\GD}{\GG}{\{e'\}}{\FS\;A}}{\J{\GD}{\cdot}{e'}{A}}
    \]

  \item[Case $\ms{let}_{\in}$:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{\letin{y}{e_1}{e_2}}{N}}{
      \J{\GD}{\GG,x\of M}{e_1}{\FS\;A} &
      \J{\GD,y\of A}{\GG,x\of M}{e_2}{N}}
    \]

    By our IHs and weakening, we have $\J{\GD}{\GG}{\sub{e/x} e_1}{\FS\;A}$
    and $\J{\GD,y\of A}{\GG}{\sub{e/x} e_2}{N}$. Thus:
    \[
    \infer{\J{\GD}{\GG}{\letin{y}{\sub{e/x}e_1}{\sub{e/x}e_2}}{N}}{
      \J{\GD}{\GG}{\sub{e/x} e_1}{\FS\;A} &
      \J{\GD,y\of A}{\GG}{\sub{e/x} e_2}{N}}
    \]

  \item[Case $\ms{fix}$:] Given \[
    \infer{\J{\GD}{\GG,x\of M}{\fix{y} e'}{N}}{
      \J{\GD}{\GG,x\of M,y\of N}{e'}{N}}
    \]

    By our IH and weakening, we have $\J{\GD}{\GG,y \of N}{\sub{e/x} e'}{N}$.
    Thus: \[
    \infer{\J{\GD}{\GG}{\fix{y} \sub{e/x} e'}{N}}{
      \J{\GD}{\GG,y\of N}{\sub{e/x} e'}{N}}
    \]

  \item[\omitted{Omitted cases:}] $(,\!)$, $\pi_i$, $\ms{in}_i$,
    $\emptyset$, and ${\vee}$ are trivial.
  \end{description}
\end{quote}
