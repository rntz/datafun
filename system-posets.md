<!-- Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod
tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam,
quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo
consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum
dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident,
sunt in culpa qui officia deserunt mollit anim id est laborum. -->

\newcommand{\op}[1]{#1^{\ms{op}}}
\newcommand{\D}[1]{\ms{D}\,#1}
\renewcommand{\J}[3]{#1 \ent #2 : #3}

# Notation

Given sets $A,B$, posets $P,Q$, and usls (unital semilattices) $M,N$, we use the
following notation:
\begin{center}
  \begin{tabular}{cl}
    $|P|$ & underlying set of the poset $P$\\
    $\op{P}$ & the opposite-ordering of $P$\\
    $P \x_\le Q$ & poset of pairs of $P$s and $Q$s, ordered pointwise\\
    $P \uplus_\le Q$ & poset on $P \uplus Q$, ordered disjointly\\
    $P \lhd Q$ & poset on $P \uplus Q$ where
    $\ms{in}_1\; x \le \ms{in}_2\; y\ (\forall x \of P,y \of Q)$\\
    $P \mono Q$ & poset of monotone maps from $P$ to $Q$\\
    $\ms{D}\,A$ & discrete poset on $A$ (where $x \le y \iff x = y$)\\
    $\FS\;A$ & usl of finite sets of $A$s, ordered by inclusion
  \end{tabular}
\end{center}

Note that $\ms{D}$ and $|\_|$ are adjoint, and that $|\ms{D}\,A| = A$.

# Language

## Syntax

$$\begin{array}{lrrl}
\text{types} & P,Q
&::=& |P| \pipe \op{P}
\pipe P \x Q \pipe P + Q \pipe P \lhd Q \pipe P \to Q\\
&&|\,& \N \pipe \FS\;A\\
\text{discrete types} & A,B
&::=& |P| \pipe A \x B \pipe A + B \pipe A \to B\\
\text{lattice types} & M,N
&::=& \N \pipe M \x N \pipe P \to M \pipe \FS\;A\\
\text{expressions} & e
&::=& x \pipe \fn\bind{x} e \pipe e_1\;e_2
\pipe (e_1,e_2) \pipe \pi_i\;e\\
&&|\,& \ms{in}_i\; e \pipe \case{e}{x}{e_1}{y}{e_2}\\
&&|\,& \emptyset \pipe u_1 \vee u_2\\
&&|\,& \{u\} \pipe \letin{x}{u_1}{u_2}\\
&&|\,& \fix{x}u\\
&&|\,& |e| \pipe e ~\ms{as}~ P\\
\text{contexts} & \GG &::=& \cdot \pipe \GG, x \of P \\
\text{typing judgments} & J &::=& \J{\GG}{e}{P}
\end{array}$$

Discrete types and lattice types are syntactic restrictions of types.

## Semantics of types

Types $P$ are interpreted as posets $\den{P}$. Discrete types $A$ will
correspond (\omitted{TODO: lemma}) to discrete posets. Lattice types $M$ will
correspond (\omitted{TODO: lemma}) to usls with computable units and joins.

Denotation of types $\den{P}$:
$$\begin{array}{rcl}
  \den{|P|} &=& \D{|\den{P}|}\\
  \den{\op{P}} &=& \op{\den{P}}\\
  \den{P \x Q} &=& \den{P} \x_\le \den{Q}\\
  \den{P + Q} &=& \den{P} \uplus_\le \den{Q}\\
  \den{P \lhd Q} &=& \den{P} \lhd \den{Q}\\
  \den{P \to Q} &=& \den{P} \mono \den{Q}\\
  \den{N} &=& \pair{\N}{\le}\\
  \den{\FS\;A} &=& \FS\;|\den{A}|
\end{array}$$

## Equality and subtyping

\omitted{I'm not sure I've gotten everything here.}

Nontrivial laws for equality of types $P = Q$:
$$\begin{array}{rclcl}
  |A| &=& A\\
  |\op{P}| &=& |P|\\
  |P \x Q| &=& |P| \x |Q|\\
  |P + Q| &=& |P| + |Q|\\
  |P \lhd Q| &=& |P| + |Q|\\
  \op{A} &=& A\\
  \op{(\op{P})} &=& P\\
  \op{(P \x Q)} &=& \op{P} \x \op{Q}\\
  \op{(P + Q)} &=& \op{P} + \op{Q}\\
  \op{(P \to Q)} &=& \op{P} \to \op{Q}\\
  \op{P} \to Q &=& P \to \op{Q}
\end{array}$$

Nontrivial laws for subtyping $P \le Q$:
$$\begin{array}{rcll}
  |P| &\le& P\\
  P + Q &\le& P \lhd Q
\end{array}$$
NB. $|P| \le \op{P}$ follows from $|P| = |\op{P}|$ and $|\op{P}| \le \op{P}$.

Moreover:\vspace{-1em}
\begin{itemize}\setlength{\itemsep}{0pt}
\item $P \x Q$ and $P + Q$ are covariant in $P$ and $Q$
\item $P \lhd Q$ is covariant in $P$ and $Q$\omitted{, I think?}
\item $P \to Q$ is covariant in $Q$ and contravariant in $P$
\item $\op{P}$ is covariant in $P$\omitted{, I think?}
\item $|P|$ is \textbf{bivariant} in $P$\omitted{, I think? I'm not sure whether
  this needs to be a rule, or follows from the rules already given}. This is b/c
  subtyping here represents \emph{order extension only}.
\end{itemize}

\textbf{Theorem:} Type equality and subtyping are decidable. \textbf{Proof:}
\omitted{TODO}.

## Typing rules

\newcommand{\dsc}[1]{|#1|_D}

We write $\dsc{\GG}$ for the \emph{discrete restriction} of a context $\GG$,
defined by:
$$\begin{array}{rcll}
  \dsc{\cdot} &=& \cdot\\
  \dsc{\GG,x\of A} &=& \dsc{\GG},x\of A\\
  \dsc{\GG,x\of P} &=& \dsc{\GG} & \text{(where $P$ is not an $A$)}
\end{array}$$

### Structural rules

These rules are technically unnecessary, as they are (ought to be, no proof yet)
admissible.

$$
\infer[\ms{exchange}]{\J{\GG_1,\GG_2}{e}{P}}{\J{\GG_2,\GG_1}{e}{P}}
\quad
\infer[\ms{weaken}]{\J{\GG,\GG'}{e}{P}}{\J{\GG}{e}{P}}
$$

### Other rules

$$
\infer[\ms{hyp}]{\J{\GG}{x}{P}}{x\of P \in \GG} \qquad
\infer[\fn]{\J{\GG}{\fn\bind{x}{e}}{P \to Q}}{
  \J{\GG,x\of P}{e}{Q}} \qquad
\infer[\ms{app}]{\J{\GG}{e_1\;e_2}{Q}}{
  \J{\GG}{e_1}{P \to Q} &
  \J{\GG}{e_2}{P}}
$$\ $$
\infer[(,\!)]{\J{\GG}{(e_1, e_2)}{P_1 \x P_2}}{\J{\GG}{e_i}{P_i}}
\qquad
\infer[\pi_i]{\J{\GG}{\pi_i\; e}{P_i}}{\J{\GG}{e}{P_1 \x P_2}}
$$\ $$
\infer[\ms{in}_i]{\J{\GG}{\ms{in}_i\;e}{P_1 + P_2}}{
  \J{\GG}{e}{P_i}} \qquad
\infer[\ms{case}]{\J{\GG}{\case{e}{x_1}{e_1}{x_2}{e_2}}{Q}}{
  \J{\GG}{e}{P_1 + P_2} &
  \J{\GG,x_i\of P_i}{e_i}{Q}}
$$\ $$
\infer[\emptyset]{\J{\GG}{\emptyset}{M}}{} \qquad
\infer[\vee]{\J{\GG}{e_1 \vee e_2}{M}}{\J{\GG}{e_i}{M}}
$$\ $$
\infer[\{\}]{\J{\GG}{\{e\}}{\FS\;A}}{\J{\dsc{\GG}}{e}{A}} \qquad
\infer[\ms{let}_{\in}]{\J{\GG}{\letin{x}{e_1}{e_2}}{M}}{
  \J{\GG}{e_1}{\FS\;A} &
  \J{\GG,x\of A}{e_2}{M}}
$$\ $$
\infer[\ms{fix}]{\J{\GG}{\fix{x}e}{M}}{
  \J{\GG,x\of M}{e}{M}}
$$\ $$
\infer[|{\cdot}|]{\J{\GG}{|e|}{|P|}}{\J{\dsc{\GG}}{e}{P}} \qquad
\infer[\ms{as}]{\J{\GG}{e~\ms{as}~P}{P}}{\J{\GG}{e}{|P|}}
$$

The \ms{fix} rule is overly permissive in allowing fix-points to be taken at any
lattice type; it needs to be be restricted to some computationally tractable
class of lattice types.

The \ms{as} rule is ``unnecessary'' in the presence of the subtyping rule that
$|P| \le P$. (Type annotations might be needed for inference, though.)
