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
\text{typing} & J &::=& \J{\GD}{\cdot}{e}{A}\\
\text{judgment} &&|\,& \J{\GD}{\GG}{e}{M}
\end{array}$$

# Typing rules

## Structural rules

$$
\infer[\ms{exchange}]{
  \J{\GD_1,\GD_2}{\GG_1,\GG_2}{e}{A}}{\J{\GD_2,\GD_1}{\GG_2,\GG_1}{e}{A}}
\qquad
\infer[\ms{weaken}]{\J{\GD,\GD'}{\GG,\GG'}{e}{A}}{\J{\GD}{\GG}{e}{A}}
$$\ $$
\infer[\ms{forget}]{\J{\GD,x\of M}{\GG}{e}{N}}{\J{\GD}{\GG,x\of M}{e}{N}}
$$

## Other rules

$$
\infer{\J{\GD,x\of A}{\GG}{x}{A}}{} \qquad
\infer{\J{\GD}{\GG,x\of M}{x}{M}}{}
$$\ $$
\infer{\J{\GD}{\GG}{\fn\bind{x}{e}}{A \to B}}{
  \J{\GD,x\of A}{\GG}{e}{B}} \qquad
\infer{\J{\GD}{\GG}{e_1\;e_2}{B}}{
  \J{\GD}{\GG}{e_1}{A \to B} &
  \J{\GD}{\cdot}{e_2}{B}}
$$\ $$
\infer{\J{\GD}{\GG}{\monofn\bind{x}{e}}{M \mono N}}{
  \J{\GD}{\GG,x \of M}{e}{N}} \qquad
\infer{\J{\GD}{\GG}{e_1\;e_2}{N}}{
  \J{\GD}{\GG}{e_1}{M \mono N} &
  \J{\GD}{\GG}{e_2}{M}}
$$
