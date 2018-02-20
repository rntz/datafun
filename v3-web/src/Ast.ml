open Sigs
open Util

(* loc ::= (start_pos, end_pos) *)
type loc = Lexing.position * Lexing.position
type var = string
type tag = string
type prim = string
module Var = struct let show x = x end
module Tag = struct let show n = n end
module Prim = struct let show p = p end


(* ----- Tones ----- *)
type tone = [`Id | `Op | `Iso | `Path]
module Tone = struct
  let show: tone -> string = function
    | `Id -> "id" | `Op -> "op" | `Iso -> "iso" | `Path -> "path"

  let meet (a: tone) (b: tone): tone = match a, b with
    | `Iso, _ | _, `Iso | `Id, `Op | `Op, `Id -> `Iso
    | x, `Path | `Path, x -> x
    | `Id, `Id | `Op, `Op -> a

  let (<=) (a: tone) (b: tone): bool = match a,b with
    | `Iso, _ | _, `Path -> true
    | `Id, `Id | `Op, `Op -> true
    | _, `Iso | `Path, _ | `Op, `Id | `Id, `Op -> false

  (* Order of composition: T_(compose s t) == (T_s . T_t)
   *
   * This is the opposite of the order I usually use in my notes,
   * where tone application is postfix, A^{s . t} == (A^s)^t.
   *)
  let compose (a: tone) (b: tone): tone = match a,b with
    | x, `Id | `Id, x -> x
    | `Op, `Op -> `Id
    | _, `Iso | _, `Path -> b   (* hi priority, must come first *)
    | `Iso, _ | `Path, _ -> a   (* lo priority, comes later *)

  let ( * ) = compose
end


(* ---------- Types ---------- *)
type base = [`Bool | `Int | `Str]
type tp =
  [ base
  | `Name of string
  | `Set of tp
  | `Box of tp
  | `Arrow of tp * tp
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
    | `Arrow(`Box a, b) -> show_product a ^ " -> " ^ show b
    | `Arrow(a, b) -> show_product a ^ " => " ^ show b
    | tp -> show_product tp
  and show_product: tp -> string = function
    | `Tuple (_::_ as tps) -> String.concat ", " (List.map show_atom tps)
    | tp -> show_atom tp
  and show_atom: tp -> string = function
    | #base as b -> Base.show b
    | `Tuple [] -> "()"
    | `Sum [] -> "<void>"
    | `Set tp -> "{" ^ show tp ^ "}"
    | `Box tp -> "!" ^ show_atom tp
    | `Name n -> Var.show n
    | tp -> "(" ^ show tp ^ ")"

  let rec discrete: tp -> bool = function
    | `Str | `Box _ -> true
    | `Arrow (_,b) -> discrete b
    | `Tuple ts -> List.for_all discrete ts
    | `Sum cs -> List.for_all (fun (_,tp) -> discrete tp) cs
    | `Bool | `Int | `Name _ | `Set _ -> false

  (* a sum type shouldn't use the same tag twice. *)
  exception Malformed of string * tp
  let well_formed: tp -> unit = function
    | _ -> raise TODO

  (* ---------- The type lattice: equality, subtyping, join/meet ---------- *)
  type how = [ `Join | `Meet | `Eq ]
  let op: how -> how = function | `Join -> `Meet | `Meet -> `Join | `Eq -> `Eq
  (* Incompatible (message, how, tp1, tp2)
   * message can be "", meaning "they're just plain incompatible"
   * eg. a sum type & a product type.
   *)
  exception Incompatible of string * how * tp * tp
  module StringMap = Map.Make(String)

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
    | `Box a, `Box b -> `Box (recur a b)
    | `Arrow(a1,b1), `Arrow(a2,b2) -> `Arrow (recurOp a1 a2, recur b1 b2)
    | `Tuple tps1, `Tuple tps2 ->
       (try `Tuple (List.map2 recur tps1 tps2)
        with Invalid_argument _ -> fail "these tuples have different lengths")
    (* oh god sums *)
    | `Sum tps1, `Sum tps2 ->
       (* tag-set union if `Join, intersection if `Meet, equality if `Eq *)
       let open StringMap in
       let toMap = List.fold_left (fun map (tag,tp) -> add tag tp map) empty in
       let combine tag a b = match a,b with
         | Some a, Some b -> Some (recur a b)
         | None, None -> None
         | Some tp, None | None, Some tp ->
            match how with
            | `Eq -> fail ("tag " ^ tag
                           ^ " is present in one type but not the other")
            | `Join -> Some tp   (* union *)
            | `Meet -> None      (* intersection *)
       in `Sum (bindings (StringMap.merge combine (toMap tps1) (toMap tps2)))

    (* (`Box a <: a), so `Box can be dropped when joining or added when meeting.
     * There are many more semantic equalities/subtypings we could try to
     * handle here, but for simplicity's sake we don't.
     *
     * For example, we do NOT handle box-tuple distributivity,
     *     `Box (`Tuple [a;b]) == `Tuple [`Box a; `Box b]
     *)
    | `Box a, b | a, `Box b when how = `Join -> recur a b
    | `Box a, b | a, `Box b when how = `Meet -> `Box (recur a b)

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
  | `Box of pat | `Tuple of pat list | `Tag of tag * pat ]

module Pat = struct
  let rec show: pat -> string = function
    | `Tuple ps -> String.concat ", " (List.map show_app ps)
    | p -> show_app p
  and show_app: pat -> string = function
    | `Box p -> "!" ^ show_app p
    | `Tag (n,p) -> n ^ " " ^ show_atom p
    | p -> show_atom p
  and show_atom: pat -> string = function
    | #lit as l -> Lit.show l
    | `Var v -> Var.show v
    | `Wild -> "_"
    | p -> "(" ^ show p ^ ")"
end


(* ---------- Expressions & declarations ---------- *)
type 'a comp = When of 'a | In of pat * 'a
type 'a decl =
  | Type of var * tp
  | Def of pat * tp option * 'a

type 'a expF =
  [ lit
  | `Var of var
  | `The of tp * 'a              (* type annotation *)
  | `Prim of prim                (* builtin functions *)
  | `Lub of 'a list
  | `Fix of pat * 'a
  | `Let of 'a decl list * 'a
  (* Introductions *)
  | `Box of 'a
  | `Lam of pat list * 'a
  | `Tuple of 'a list | `Tag of tag * 'a
  | `Set of 'a list
  (* Eliminations *)
  | `Unbox of 'a
  | `App of 'a * 'a
  | `For of 'a comp list * 'a
  (* (if M then N else O) is parsed as (case M of true => N | false => O) *)
  | `Case of 'a * (pat * 'a) list ]

(* NB. An equirecursive type! *)
type 'a exp = 'a * 'a exp expF
type expr = loc exp

type 'a expAlgebra = 'a expF -> 'a

(* (\* Expression algebras.
 *  * I could use objects for this, but don't.*\)
 * type 'a expAlg =
 *   { lit: lit -> 'a
 *   ; var: var -> 'a
 *   ; the: tp * 'a -> 'a
 *   ; prim: prim -> 'a
 *   ; lub: 'a list -> 'a
 *   ; fix: pat * 'a -> 'a
 *   ; let_: 'a decl list * 'a -> 'a
 *   ; box: 'a -> 'a
 *   ; lam: pat list * 'a -> 'a
 *   ; tuple: 'a list -> 'a
 *   ; tag: tag * 'a -> 'a
 *   ; set: 'a list -> 'a
 *   ; unbox: 'a -> 'a
 *   ; app: 'a * 'a -> 'a
 *   ; for_: 'a comp list * 'a -> 'a
 *   ; case: 'a * (pat * 'a) list -> 'a }
 * 
 * (\* this makes using expression algebras more convenient. *\)
 * let algebra (alg: 'a expAlgebra): 'a expAlg =
 *   { lit   = (fun l -> alg (l :> 'a expF))
 *   ; var   = (fun l -> alg (`Var l))
 *   ; the   = (fun x -> alg (`The x))
 *   ; prim  = (fun x -> alg (`Prim x))
 *   ; lub   = (fun x -> alg (`Lub x))
 *   ; fix   = (fun x -> alg (`Fix x))
 *   ; let_  = (fun x -> alg (`Let x))
 *   ; box   = (fun x -> alg (`Box x))
 *   ; lam   = (fun x -> alg (`Lam x))
 *   ; tuple = (fun x -> alg (`Tuple x))
 *   ; tag   = (fun x -> alg (`Tag x))
 *   ; set   = (fun x -> alg (`Set x))
 *   ; unbox = (fun x -> alg (`Unbox x))
 *   ; app   = (fun x -> alg (`App x))
 *   ; for_  = (fun x -> alg (`For x))
 *   ; case  = (fun x -> alg (`Case x))
 *   } *)


(* ----- Traversing expressions ----- *)
module Comp = Traverse(struct
  type 'a t = 'a comp
  module Seq(M: IDIOM) = struct
    open M
    let traverse (f : 'a -> 'b M.t) : 'a comp -> 'b comp M.t = function
      | When a -> map (fun x -> When x) (f a)
      | In (p,a) -> map (fun x -> In (p,x)) (f a)
  end
end)

module Decl = struct
  include Traverse(struct
    type 'a t = 'a decl
    module Seq(M: IDIOM) = struct
      open M
      let traverse f = function
        | Type(x,t) -> pure (Type(x,t))
        | Def(p,t,e) -> map (fun x -> Def(p,t,x)) (f e)
        (* | Ascribe(xs,t) -> pure (Ascribe(xs,t))
         * | Define(x,args,body) -> map (fun body' -> Define(x, args, body')) (f body)
         * | Decons(p,e) -> map (fun x -> Decons(p,x)) (f e) *)
    end
  end)

  let show (f: 'a -> string): 'a decl -> string = function
    | Type (v, tp) ->
       Printf.sprintf "type %s = %s" (Var.show v) (Type.show tp)
    | Def (p, None, x) ->
       Printf.sprintf "def %s = %s" (Pat.show_atom p) (f x)
    | Def (p, Some tp, x) ->
       Printf.sprintf "def %s: %s = %s" (Pat.show_atom p) (Type.show tp) (f x)
    (* | Ascribe (xs, tp) -> String.concat " " xs ^ " : " ^ Type.show tp
     * | Define (x,ps,body) ->
     *    [Var.show x] @ List.map Pat.show_atom ps @ ["="; show body]
     *    |> String.concat " "
     * | Decons (p,e) -> Pat.show p ^ " = " ^ show e *)
end

module ExpT: TRAVERSABLE with type 'a t = 'a expF = struct
  type 'a t = 'a expF
  module Seq(M: IDIOM) = struct
    open M
    module DeclSeq = Decl.Seq(M)
    module CompSeq = Comp.Seq(M)

    (* I find myself wanting lenses. *)
    let traverse (f: 'a -> 'b M.t) = function
      | #lit as l -> pure l
      | `Var x -> pure (`Var x)
      | `The(t,e) -> f e => fun x -> `The (t, x)
      | `Prim s -> pure (`Prim s)
      | `Lub es -> forEach es f => fun x -> `Lub x
      | `Fix (x,e) -> f e => fun e -> `Fix (x,e)
      | `Let (ds, e) -> forEach ds (DeclSeq.traverse f) ** f e
                        => fun(ds,e) -> `Let(ds,e)
      (* introductions *)
      | `Box e -> f e => fun x -> `Box x
      | `Lam(x,e) -> f e => fun e -> `Lam (x, e)
      | `Tuple es -> forEach es f => fun xs -> `Tuple xs
      | `Tag(n,e) -> f e => fun e -> `Tag(n,e)
      | `Set es -> forEach es f => fun xs -> `Set xs
      (* eliminations *)
      | `Unbox e -> f e => fun x -> `Unbox x
      | `App (e1, e2) -> f e1 ** f e2 => fun (x,y) -> `App(x,y)
      | `For (cs, e) ->
         forEach cs (CompSeq.traverse f) ** f e
         => fun (cs,e) -> `For(cs,e)
      | `Case (e, arms) ->
         f e ** forEach arms (fun(p,x) -> pure p ** f x)
         => fun(e,arms) -> `Case(e,arms)
  end
end

module Exp = struct
  include Traverse(ExpT)

  (* TODO: use Format module to write a pretty-printer.
   * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html *)
  let rec show ((_, e) as expr: 'a exp) = match e with
    | `The (a,x) -> "the " ^ Type.show_atom a ^ " " ^ show x
    | `Fix (x,e) -> Pat.show_atom x ^ " as " ^ show e
    | `Let (ds,e) ->
       let show_decls = List.map (Decl.show show)
       in ["let"] @ show_decls ds @ ["in"; show e] |> String.concat " "
    (* introductions *)
    | `Lam (ps, e) ->
       ["fn"] @ List.map Pat.show_atom ps @ ["->"; show e]
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
  and show_infix ((_,e) as expr: 'a exp) = match e with
    | `Tuple (_::_::_ as es) -> List.map show_app es |> String.concat ", "
    | `Lub (_::_ as es) -> List.map (fun x -> "or " ^ show_app x) es |> String.concat " "
    | _ -> show_app expr
  and show_app ((_,e) as expr: 'a exp) = match e with
    | `App (e1,e2) -> show_app e1 ^ " " ^ show_atom e2
    | `Tag (n,e) -> Tag.show n ^ " " ^ show_atom e
    | `Box e -> "box " ^ show_atom e
    | `Unbox e -> "unbox " ^ show_atom e
    | _ -> show_atom expr
  and show_atom ((_,e) as expr: 'a exp) = match e with
    | #lit as l -> Lit.show l
    | `Var x -> Var.show x
    | `Prim p -> Prim.show p
    | `Lub [] -> "empty"
    | `Tuple [e] -> "(" ^ show_app e ^ ",)"
    | `Tuple [] -> "()"
    | `Set es -> "{" ^ String.concat ", " (List.map show es) ^ "}"
    | _ -> "(" ^ show expr ^ ")"
end
