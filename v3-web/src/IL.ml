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
  | `Var of var
  | `Let of (pat * exp) list * exp
  | `Lub of semilat * exp list
  | `Prim of Prim.prim
  (* Fix(how, x, step): fixed point of (\x.step) starting from init *)
  | `Fix of fix * pat * exp
  (* introductions *)
  | `Lam of pat * exp | `Tuple of exp list | `Tag of tag * exp
  | `Set of exp list
  (* eliminations *)
  | `App of exp * exp
  (* For(howToJoin, comps, bodyExp) *)
  | `For of semilat * comp list * exp
  | `Case of exp * (pat * exp) list ]

and comp =
  [ `When of exp
  | `In of pat * exp ]

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

exception NotFix of Ast.tp
let rec fix (unroll: string -> Ast.tp): Ast.tp -> fix = function
  | `Name n -> fix unroll (unroll n)
  | `Bool -> `Bool
  | `Set _ -> `Set
  | `Tuple ts -> `Tuple (List.map (fix unroll) ts)
  | `Fn _ | `Sum _ | `Int | `Str as tp -> raise (NotFix tp)

module Pat = struct
  let rec show p = show_infix p
  and show_infix = function
    | `Tuple ps -> List.map show_app ps |> String.concat ","
    | p -> show_app p
  and show_app = function
    | `Tag (n,p) -> n ^ " " ^ show_atom p
    | p -> show_atom p
  and show_atom = function
    | `Wild -> "_"
    | `Var v -> v
    | `Eq (_, `Var v) -> "=" ^ v
    | `Eq (_, _) -> "=<expr>"
    | p -> "(" ^ show p ^ ")"
end
