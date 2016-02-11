\textcolor{red}{NOTE: actually, we can interpret types as \emph{sets equipped
    with reflexive relations} --- a generalization of posets.}

\newcommand{\op}[1]{#1^{\ms{op}}}
\newcommand{\D}[1]{\ms{D}\,#1}
\newcommand{\disc}[1]{\ms{disc}\;#1}

# Notation

Given sets $A,B$, posets $P,Q$, and usls (unital semilattices) $M,N$, we use the
following notation:
\begin{center}
  \begin{tabular}{cl}
    $|P|$ & underlying set of the poset $P$\\
    $P \x_\le Q$ & poset of pairs of $P$s and $Q$s, ordered pointwise\\
    $P +_\le Q$ & poset on the disjoint sum of $P$ and $Q$, ordered disjointly\\
    $P \lhd Q$ & poset on the disjoint sum of $P$ and $Q$ where
    $\ms{in}_1\; x \le \ms{in}_2\; y\ (\forall x \of P,y \of Q)$\\
    $P \mto Q$ & poset of monotone maps from $P$ to $Q$\\
    $\D{A}$ & discrete poset on $A$ (where $x \le y \iff x = y$)\\
    $\FS\;A$ & usl of finite sets of $A$s, ordered by inclusion
  \end{tabular}
\end{center}

Note that $\ms{D}$ and $|\_|$ are adjoint, and that $|\ms{D}\,A| = A$.

# Language

## Syntax

$$\begin{array}{lrrl}
\text{types} & A,B
&::=& |P| \pipe A \x B \pipe A + B \pipe A \to B\\
\text{poset types} & P,Q
&::=& \ms{D}\;A \pipe P^{\ms{op}}
\pipe P \x Q \pipe P + Q \pipe P \lhd Q \pipe P \to Q\\
&&|\,& \N \pipe \FS\;A\\
\text{lattice types} & M,N
&::=& \N \pipe M \x N \pipe P \to M \pipe \FS\;A\\
\text{expressions} & e
&::=& x \pipe \fn\bind{x} e \pipe e_1\;e_2
\pipe (e_1,e_2) \pipe \pi_i\;e\\
&&|\,& \ms{in}_i\; e \pipe \case{e}{x}{e_1}{y}{e_2}\\
&&|\,& |u|\\
\text{monotone exprs} & u
&::=& x \pipe \fn\bind{x} u \pipe u_1\;u_2 \pipe (u_1, u_2) \pipe \pi_i\;u\\
%% &&|\,& e \pipe \ms{let}~|x : P| = u_1 ~\ms{in}~ u_2 \\
&&|\,& \ms{in}_i\; u \pipe \case{u}{x}{u_1}{y}{u_2}\\
&&|\,& \emptyset \pipe u_1 \vee u_2\\
&&|\,& \{u\} \pipe \letin{x}{u_1}{u_2}\\
&&|\,& \fix{x}{u}\\
&&|\,& e ~\ms{as}~ P
\pipe \disc{e} ~|~ \ms{let}~\disc{x} = u_1 ~\ms{in}~ u_2\\
\text{contexts} & \GD &::=& \cdot \pipe \GD, x \of A \\
\text{monotone ctxts} & \GG &::=& \cdot \pipe \GG, x \of P\\
\text{typing judgments} & J &::=& \GD\ent e : A\\
&&|\,& \J{\GD}{\GG}{u}{P}
\end{array}$$

Note that:\vspace{-0.8em}
\begin{itemize}
  \setlength{\itemsep}{0em}
\item Type and poset types are separate, although sharing the overloaded
  notation $\x$, $+$ and $\to$.
\item Lattice types are a syntactic restriction of poset types.
\end{itemize}

## Semantics of types

\newcommand{\setden}[1]{\den{#1}_{\ms{set}}}
\newcommand{\posden}[1]{\den{#1}_{\ms{pos}}}
\newcommand{\latden}[1]{\den{#1}_{\ms{usl}}}

Types $A$ are interpreted as sets $\setden{A}$. Poset types $P$ are interpreted
as posets $\posden{P}$. As a lemma (\omitted{TODO: prove}), the denotation
$\posden{M}$ of a lattice type $M$ is always an usl with computable unit and
join.

Denotation of types $\setden{A}$:
$$\begin{array}{rcl}
  \setden{|P|} &=& |\posden{P}|\\
  \setden{A \x B} &=& \setden{A} \x \setden{B}\\
  \setden{A + B} &=& \setden{A} \uplus \setden{B}\\
  \setden{A \to B} &=& \setden{A} \to \setden{B}
\end{array}$$

Denotation of posets $\posden{P}$:
$$\begin{array}{rcl}
  \posden{\D{A}} &=& \D{\setden{A}}\\
  \posden{\N} &=& \pair{\N}{\le}\\
  \posden{P \x Q} &=& \posden{P} \x_\le \posden{Q}\\
  \posden{P + Q} &=& \posden{P} +_\le \posden{Q}\\
  \posden{P \lhd Q} &=& \posden{P} \lhd \posden{Q}\\
  \posden{P \to Q} &=& \posden{P} \mto \posden{Q}\\
  \posden{\FS\;A} &=& \FS\;\setden{A}
\end{array}$$

## Equality and subtyping

\omitted{I'm not sure I've gotten everything here.}

Nontrivial laws for equality of types $A = B$:
$$
\begin{array}{rcl}
  |P \x Q| &=& |P| \x |Q|\\
  |P + Q| &=& |P| + |Q|\\
  |P \lhd Q| &=& |P| + |Q|\\
  |\ms{D}\,A| &=& A\\
  |\D{A} \to P| &=& A \to |P|\\
\end{array}$$

Nontrivial laws for equality of posets $P = Q$:
$$\begin{array}{rclcl}
  \D{(A \x B)} &=& \D{A} \x \D{B}\\
  \D{(A + B)} &=& \D{A} + \D{B}\\
  \D{(A \to B)} &=& \D{A} \to \D{B}\\
  \D{|P \to \D{A}|} &=& P \to \D{A}
  & \text{\omitted{is this true? necessary?}}\\
  \op{(\op{P})} &=& P\\
  \op{(P \x Q)} &=& \op{P} \x \op{Q}\\
  \op{(P + Q)} &=& \op{P} + \op{Q}\\
  \op{(P \to Q)} &=& \op{P} \to \op{Q}\\
  \op{P} \to Q &=& P \to \op{Q}
\end{array}$$

Nontrivial laws for subtyping of posets $P \le Q$:
$$\begin{array}{rcl}
  \D{|P|} &\le& P\\
  P + Q &\le& P \lhd Q
\end{array}$$
Moreover:\vspace{-0.8em}
\begin{itemize}\setlength{\itemsep}{0pt}
\item ${\x}$, ${+}$, $\lhd$, and $\op{\_}$ are covariant
\item $P \to Q$ is covariant in $Q$ and contravariant in $P$
\item \FS{} and \ms{D} are covariant (although I'm not sure there are any
  non-reflexive subtyping relations $A \le B$)
\end{itemize}

\textbf{Theorem:} Type equality and subtyping are decidable. \textbf{Proof:}
\omitted{TODO}.

## Typing rules
\newcommand{\K}[3]{#1 \ent #2 : #3}

### Interesting rules for $\K{\GD}{e}{A}$

$$
\infer[\ms{hyp}]{\K{\GD}{x}{A}}{x\of A \in \GD} \qquad
\infer[\ms{cast}]{\K{\GD}{e}{B}}{\K{\GD}{e}{A} & A \le B} \qquad
\infer[|{\cdot}|]{\K{\GD}{|u|}{|P|}}{\J{\GD}{\cdot}{u}{P}}
$$

### Interesting rules for $\J{\GD}{\GG}{u}{P}$

$$
\infer[\ms{hyp}]{\J{\GD}{\GG}{x}{P}}{x\of P \in \GG} \qquad
\infer[\ms{cast}]{\J{\GD}{\GG}{u}{Q}}{\J{\GD}{\GG}{u}{P} & P \le Q} \qquad
\infer[\ms{op}]{\J{\GD}{\GG}{\op{u}}{\op{P}}}{\J{\GD}{\op{\GG}}{u}{P}}
$$\ $$
\infer[\ms{as}]{\J{\GD}{\GG}{e~\ms{as}~P}{P}}{\K{\GD}{e}{|P|}} \qquad
\infer[\ms{disc}]{\J{\GD}{\GG}{\disc{e}}{\D{A}}}{\K{\GD}{e}{A}} \qquad
\infer[\ms{let}_{\ms{disc}}]{
  \J{\GD}{\GG}{\ms{let}~\disc{x} = u_1 ~\ms{in}~ u_2}{P}
}{
  \J{\GD}{\GG}{u_1}{\D{A}} &
  \J{\GD,x \of A}{\GG}{u_2}{P}
}
$$\ $$
\infer[\emptyset]{\J{\GD}{\GG}{\emptyset}{M}}{} \qquad
\infer[\vee]{\J{\GD}{\GG}{u_1 \vee u_2}{M}}{\J{\GD}{\GG}{u_i}{M}}
$$\ $$
\infer[\{\}]{\J{\GD}{\GG}{\{e\}}{\FS\;A}}{\K{\GD}{e}{A}} \qquad
\infer[\ms{let}_{\in}]{\J{\GD}{\GG}{\letin{x}{u_1}{u_2}}{M}}{
  \J{\GD}{\GG}{u_1}{\FS\;A} &
  \J{\GD,x\of A}{\GG}{u_2}{M}}
$$\ $$
\infer[\ms{fix}]{\J{\GD}{\GG}{\fix{x}{u}}{M}}{
  \J{\GD}{\GG,x\of M}{u}{M}}
$$

Our ``adjoint rules'' are $|{\cdot}|$, \ms{as}, \ms{disc} and
$\ms{let}_{\ms{disc}}$, and they are perfectly standard. However, \ms{as} is
unnecessary given \ms{cast}, \ms{disc}, and $\D{|P|} \le P$. However, I suspect
that if we \emph{do} have \ms{as}, we can get rid of \ms{cast} and subtyping
altogether. It's not clear which is a more ergonomic solution.

\emph{Except}... \ms{op} really wants subtyping, or else you need another
context for ``antitone variables''.

The \ms{fix} rule is overly permissive in allowing fix-points to be taken at any
lattice type; it needs to be be restricted to some computationally tractable
class of lattice types.

\omitted{TODO: denotational semantics of terms}
