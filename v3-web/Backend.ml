type pointed =
  [ `Bool | `Set | `Tuple of pointed list ]

type semilat =
  [ `Bool | `Set
  | `Tuple of semilat list
  | `Func of semilat ]

type equal =
  [ Ast.base
  | `Set of equal
  | `Tuple of equal list
  | `Sum of (Ast.tag * equal) list ]

(* Names are merely hints, to increase readability. For binding purposes
 * we use DeBruijn indices. *)
type name = string option

(* TODO: think about how I would compile pattern-matching to JS.
 * hmmmm. *)
type pat =
  [ `Wild                       (* does not bind! no DeBruijn index! *)
  | `Var of name
  | `Tuple of pat list | `Tag of Ast.tag * pat
  (* binding order is left-to-right; this `exp` sees all variables
   * preceding it in the pattern. *)
  | `Eq of equal * exp
  (* | `When of pat * exp *)
  ]

and exp =
  [ Ast.lit
  | `Stuck of string            (* unrecoverable error *)
  | `Var of int                 (* debruijn index *)
  (* Let(x, e, body): "let x = e in body" *)
  | `Let of name * exp * exp
  | `Lub of semilat * exp list | `Eq of equal * exp * exp
  (* Fix(init, x, step): fixed point of (\x.step) starting from init *)
  | `Fix of exp * name * exp
  (* introductions *)
  | `Lam of name * exp | `Tuple of exp list | `Tag of Ast.tag * exp
  | `MkSet of exp list
  (* eliminations *)
  | `App of exp * exp
  | `IfThenElse of exp * exp * exp
  (* For(howToJoin, setExp, (x, bodyExp)) *)
  | `For of semilat * exp * (name * exp)
  | `Case of exp * (pat * exp) list ]

let rec point: pointed -> exp = function
  | `Bool -> `Bool false
  | `Set -> `MkSet []
  | `Tuple ts -> `Tuple (List.map point ts)
