open Sigs
open Util
open Ast

type equal =
  [ Ast.base
  | `Set of equal
  | `Tuple of equal list
  | `Sum of (Ast.tag * equal) list ]
type semilat = [ `Bool | `Set | `Tuple of semilat list | `Fn of semilat ]
type fix = [ `Bool | `Set | `Tuple of fix list ]

type pat =
  [ `Wild
  | `Var of var
  | `Tuple of pat list | `Tag of Ast.tag * pat
  (* binding order is left-to-right; this `exp` sees all variables
   * preceding it in the pattern. *)
  | `Eq of equal * exp ]

and exp =
  [ lit
  (* | `Stuck of string            (\* do we need this? *\) *)
  | `Var of var
  | `Let of pat * exp * exp
  | `Lub of semilat * exp list | `Eq of equal * exp * exp
  (* Fix(how, x, step): fixed point of (\x.step) starting from init *)
  | `Fix of fix * var * exp
  (* introductions *)
  | `Lam of pat * exp | `Tuple of exp list | `Tag of tag * exp
  | `Set of exp list
  (* eliminations *)
  | `App of exp * exp
  (* For(howToJoin, setExp, (x, bodyExp)) *)
  | `For of semilat * exp * (var * exp)
  | `Case of exp * (pat * exp) list ]

exception NoEquality of Ast.tp
let rec equal (unroll: string -> Ast.tp): Ast.tp -> equal = function
  | `Name n -> equal unroll (unroll n)
  | #base as b -> b
  | `Set a -> `Set (equal unroll a)
  | `Tuple xs -> `Tuple (List.map (equal unroll) xs)
  | `Sum nts -> `Sum (List.map (fun (n,t) -> (n, equal unroll t)) nts)
  | `Fn _ as tp -> raise (NoEquality tp)

exception NotSemilattice of Ast.tp
let rec semilattice (unroll: string -> Ast.tp): Ast.tp -> semilat = function
  | `Name n -> semilattice unroll (unroll n)
  | `Bool -> `Bool
  | `Set _ -> `Set
  | `Fn (_,_,b) -> `Fn (semilattice unroll b)
  | `Tuple ts -> `Tuple (List.map (semilattice unroll) ts)
  | `Sum _ | `Int | `Str as tp -> raise (NotSemilattice tp)
