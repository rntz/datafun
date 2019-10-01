(* Compiling to Haskell. *)
open Util open Type open StringBuilder

type tp = rawtp
type term = StringBuilder.t

let sym x = string (Sym.to_uid x)
let paren t = string "(" ^ t ^ string ")"
let parenSpaces xs = paren (concat (string " ") xs)
let commas = concat (string ", ")
let listOf terms = string "[" ^ commas terms ^ string "]"
let call name args = parenSpaces (string name :: args)
let letBind pat expr body =
  parenSpaces [string "let"; pat; string "="; expr; string "in"; body]

let var _tp x = sym x
let letIn _a _b x expr body = letBind (sym x) expr body
let equals _a m n = parenSpaces [m; string "=="; n]
let lam _a _b x body = paren (string "\\" ^ sym x ^ string " -> " ^ body)
let app _a _b fnc arg = parenSpaces [fnc; arg]

let bool b = string (if b then "True" else "False")
let ifThenElse _tp cond thn els =
  parenSpaces [string "if"; cond; string "then"; thn; string "else"; els]
let guard _tp cond body = call "guard" [cond; body]

let tuple = function
  | [] -> string "()"
  | [_,term] -> term (* singleton tuples turn into the contained type *)
  | terms -> paren (commas List.(map snd terms))
let letTuple tpxs _bodyTp tuple body =
  letBind (List.map (fun (_tp,x) -> sym x) tpxs |> commas |> paren) tuple body
let proj tps i term = match List.length tps, i with
  | x, y when y >= x -> impossible "out of bounds projection"
  | 1, 0 -> term     (* singleton tuples turn into the contained type *)
  | 2, 0 -> call "fst" [term]
  | 2, 1 -> call "snd" [term]
  | _, _ -> todo "projection from ternary or larger tuples unimplemented"

(* NB. You'd think we could just generate "empty" here and let Haskell's
 * typeclasses do the work for us, but if Haskell can't infer the type of
 * such an expression it gets mad. So we make it explicit. *)
let rec empty: tp semilat -> term = function
  | `Bool -> string "False"
  | `Set _ -> string "Set.empty"
  | `Tuple tps -> tuple (List.map (fun tp -> tp, empty tp) tps)
  (* NB. Even if we don't treat functions as semilattice types in source code,
   * Simplify can generate them by rewriting (λx.⊥) → ⊥. *)
  | `Fn(a,b) -> lam a b (Sym.gen "_") (empty b)

let set _a terms = call "set" [listOf terms]
let union tp = function
  | [] -> empty tp
  | [tm] -> tm
  | [tm1; tm2] -> call "union" [tm1; tm2]
  | terms -> call "unions" [listOf terms]

let forIn a b x set body = call "forIn" [set; lam a b x body]
let fix _tp term = call "fix" [term]
let semifix _tp term = call "semifix" [term]

(* This has to come at the end because we use string to mean
   StringBuilder.string earlier. *)
let string s = StringBuilder.string (Printf.sprintf "%S" s)
