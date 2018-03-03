open Util

(* loc ::= (start_pos, end_pos) *)
type loc = Lexing.position * Lexing.position
type var = string
type tag = string
type tone = Tone.tone
module Var = struct let show x = x end
module Tag = struct let show n = n end

let dummy_loc = Lexing.(dummy_pos, dummy_pos)


(* ---------- Types ---------- *)
type base = [`Bool | `Int | `Str]
type tp =
  [ base
  | `Name of string
  | `Set of tp
  | `Fn of tone * tp * tp
  | `Tuple of tp list
  | `Sum of (tag * tp) list ]

module Base = struct
  let eq: base -> base -> bool = (=)
  let show: base -> string = function
    | `Bool -> "bool" | `Int -> "int" | `Str -> "str"
end

module Type = struct
  let rec show: tp -> string = function
    | `Sum (_::_ as ctors) ->
       let show_ctor (tag, tp) = match tp with
         | `Tuple [] -> Tag.show tag
         | tp -> Tag.show tag ^ " " ^ show_atom tp
       in String.concat " | " (List.map show_ctor ctors)
    | tp -> show_arrow tp
  and show_arrow: tp -> string = function
    | `Fn(`Id, a ,b) -> show_product a ^ " => " ^ show_arrow b
    | `Fn(`Iso, a, b) -> show_product a ^ " -> " ^ show_arrow b
    | `Fn(`Op, a, b) -> show_product a ^ " =>- " ^ show_arrow b
    | tp -> show_product tp
  and show_product: tp -> string = function
    | `Tuple (_::_ as tps) -> String.concat ", " (List.map show_atom tps)
    | tp -> show_atom tp
  and show_atom: tp -> string = function
    | #base as b -> Base.show b
    | `Tuple [] -> "()"
    | `Sum [] -> "<void>"
    | `Set tp -> "{" ^ show tp ^ "}"
    | `Name n -> Var.show n
    | tp -> "(" ^ show tp ^ ")"

  (* Well-formedness means:
   * - A sum type shouldn't use the same tag twice.
   *
   * - All type names are bound. If `deep` is true, we also check the types
   *   they're bound to are well-formed. If we keep the invariant that all
   *   types in the context are well-formed, then it's safe to let "deep" be
   *   false.
   *)
  type malformed = [ `RepeatedTag of tag ]
  exception Malformed of tp * malformed
  let rec typeOk (unroll: var -> tp) ~deep:deep (tp: tp): unit =
    let kids = match tp with
      | #base -> [] | `Set tp -> [tp] | `Fn(_,a,b) -> [a;b] | `Tuple tps -> tps
      |  `Name n -> let tp = unroll n in if deep then [tp] else []
      | `Sum tagtps -> let (_tags,tps) = List.split tagtps in
                       (* TODO: check uniqueness of tags *)
                       tps
    in List.iter (typeOk unroll ~deep: deep) kids

  (* ---------- The type lattice: equality, subtyping, join/meet ---------- *)
  type how = [ `Join | `Meet | `Eq ]
  let op: how -> how = function | `Join -> `Meet | `Meet -> `Join | `Eq -> `Eq
  (* Incompatible (message, how, tp1, tp2)
   * message can be "", meaning "they're just plain incompatible"
   * eg. a sum type & a product type.
   *)
  exception Incompatible of string * how * tp * tp

  let rec merge (unroll: var -> tp) (how: how) (tp1: tp) (tp2: tp): tp =
    let fail msg = raise (Incompatible (msg, how, tp1, tp2)) in
    let recur = merge unroll how in
    let recurOp = merge unroll (op how) in

    match tp1,tp2 with
    (* handling named types *)
    | `Name n, `Name m when n = m -> tp1
    | `Name n, b -> recur (unroll n) b
    | a, `Name m -> recur a (unroll m)

    (* congruence rules *)
    | #base, #base -> if tp1 = tp2 then tp1 else fail ""
    | `Set a, `Set b -> `Set (recur a b)
    | `Fn(s,a1,b1), `Fn(t,a2,b2) ->
       let combine = match how with
         | `Meet -> Tone.join | `Join -> Tone.meet
         | `Eq -> fun s t -> if s = t then s else fail "different tones"
       in `Fn (combine s t, recurOp a1 a2, recur b1 b2)
    | `Tuple tps1, `Tuple tps2 ->
       (try `Tuple (List.map2 recur tps1 tps2)
        with Invalid_argument _ -> fail "these tuples have different lengths")
    (* oh god sums *)
    | `Sum tps1, `Sum tps2 ->
       (* tag-set union if `Join, intersection if `Meet, equality if `Eq *)
       let combine tag a b = match a,b with
         | Some a, Some b -> Some (recur a b)
         | None, None -> None
         | Some tp, None | None, Some tp ->
            match how with
            | `Eq -> fail ("tag " ^ tag
                           ^ " is present in one type but not the other")
            | `Join -> Some tp   (* union *)
            | `Meet -> None      (* intersection *)
       in `Sum Dict.(bindings (merge combine (of_list tps1) (of_list tps2)))

    (* all rules tried, no solution found *)
    | _, _ -> fail ""

  let join unroll = merge unroll `Join
  let meet unroll = merge unroll `Meet
  let eq unroll a b =
    try ignore (merge unroll `Eq a b); true
    with Incompatible _ -> false

  (* Lattice law: (a ≤ b) iff (a ∨ b) = b. *)
  let subtype unroll a b =
    try eq unroll b (join unroll a b)
    with Incompatible _ -> false
end


(* ---------- Literals ---------- *)
type lit = [ `Bool of bool | `Int of int | `Str of string ]
module Lit = struct
  let show: lit -> string = function
    | `Bool true -> "true" | `Bool false -> "false"
    | `Int n -> Printf.sprintf "%d" n
    | `Str s -> Printf.sprintf "%S" s

  let typeOf: lit -> [> base ] = function
    | `Bool _ -> `Bool | `Int _ -> `Int | `Str _ -> `Str
end


(* ---------- Patterns ----------*)
type pat =
  [ lit
  | `Wild | `Var of var
  | `Tuple of pat list | `Tag of tag * pat ]

module Pat = struct
  let rec show: pat -> string = function
    | `Tuple ps -> String.concat ", " (List.map show_app ps)
    | p -> show_app p
  and show_app: pat -> string = function
    | `Tag (n,p) -> n ^ " " ^ show_atom p
    | p -> show_atom p
  and show_atom: pat -> string = function
    | #lit as l -> Lit.show l
    | `Var v -> Var.show v
    | `Wild -> "_"
    | p -> "(" ^ show p ^ ")"
end


(* ---------- Expressions & declarations ---------- *)
type expr = loc * exp
and exp =
  [ lit
  | `Var of var
  | `The of tp * expr              (* type annotation *)
  | `Prim of Prim.prim             (* builtin functions *)
  | `Lub of expr list
  | `Fix of pat * expr
  | `Let of decl list * expr
  (* Introductions *)
  | `Lam of pat list * expr
  | `Tuple of expr list | `Tag of tag * expr
  | `Set of expr list
  (* Eliminations *)
  | `App of expr * expr
  | `For of comp list * expr
  (* (if M then N else O) is parsed as (case M of true => N | false => O) *)
  | `Case of expr * (pat * expr) list ]

and comp = When of expr | In of pat * expr
and decl =
  | Type of var * tp
  | Def of pat * tone option * tp option * expr
  | Shadow of var list


(* ----- Traversing expressions ----- *)
module Expr = struct
  (* TODO: use Format module to write a pretty-printer.
   * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html *)
  let rec show ((_, e) as expr: expr): string = match e with
    | `The (a,x) -> "the " ^ Type.show_atom a ^ " " ^ show x
    | `Fix (x,e) -> Pat.show_app x ^ " as " ^ show e
    | `Let (ds,e) ->
       ["let"] @ List.map show_decl ds @ ["in"; show e] |> String.concat " "
    (* introductions *)
    | `Lam (ps, e) ->
       ["fn"] @ List.map Pat.show_atom ps @ ["=>"; show e]
       |> String.concat " "
    (* eliminations *)
    | `For (cs, e) ->
       let show_comp = function
         | When e -> show_app e
         | In (p,e) -> Pat.show_app p ^ " in " ^ show_app e
       in "for (" ^ String.concat ", " (List.map show_comp cs) ^ ") " ^ show e
    | `Case (e, pes) ->
       let show_branch (p,e) = Pat.show p ^ " -> " ^ show_infix e
       in "case " ^ show_infix e ^ String.concat "| " (List.map show_branch pes)
    | _ -> show_infix expr
  and show_infix ((_,e) as expr: expr) = match e with
    (* TODO: show applications of infix operators nicely *)
    | `Tuple (_::_::_ as es) -> List.map show_app es |> String.concat ", "
    | `Lub (_::_ as es) -> List.map (fun x -> "or " ^ show_app x) es |> String.concat " "
    | _ -> show_app expr
  and show_app ((_,e) as expr: expr) = match e with
    | `App (e1,e2) -> show_app e1 ^ " " ^ show_atom e2
    | `Tag (n,e) -> Tag.show n ^ " " ^ show_atom e
    | _ -> show_atom expr
  and show_atom ((_,e) as expr: expr) = match e with
    | #lit as l -> Lit.show l
    | `Var x -> Var.show x
    | `Prim p -> Prim.show p
    | `Lub [] -> "empty"
    | `Tuple [e] -> "(" ^ show_app e ^ ",)"
    | `Tuple [] -> "()"
    | `Set es -> "{" ^ String.concat ", " (List.map show_app es) ^ "}"
    | _ -> "(" ^ show expr ^ ")"

  and show_decl: decl -> string = function
    | Type (v, tp) ->
       Printf.sprintf "type %s = %s" (Var.show v) (Type.show tp)
    | Def (p, tone, tp, x) ->
       let showTone = function `Id -> "+" | `Iso -> "!" | `Op -> "-" | `Path -> "~" in
       let tone = Option.elim "" showTone tone in
       let tp = Option.elim "" (fun a -> ": " ^ Type.show a) tp in
       Printf.sprintf "def%s %s%s = %s" tone tp (Pat.show_atom p) (show x)
    | Shadow vars -> "shadow " ^ String.concat " " vars

  and show_decls decls = List.map show_decl decls |> String.concat " "
end
