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


(* ---------- types ---------- *)
type tone = [`Mono | `Anti | `Isos | `Path]
type base = [`Bool | `Int | `Str]
module Base = struct
  let show: base -> string = function
    | `Bool -> "bool" | `Int -> "int" | `Str -> "str"
end

type tp =
  [ base
  | `Name of var
  | `Set of tp
  | `Box of tp
  | `Arrow of tp * tp
  | `Product of tp list
  (* TODO: use hashtable? *)
  | `Sum of (tag * tp) list ]

module Type = struct
  type t = tp

  let rec show: tp -> string = function
    | `Sum (_::_ as ctors) ->
       let show_ctor (tag, tp) = match tp with
         | `Product [] -> Tag.show tag
         | tp -> Tag.show tag ^ " " ^ show_atom tp
       in String.concat " | " (List.map show_ctor ctors)
    | tp -> show_arrow tp
  and show_arrow: tp -> string = function
    | `Arrow(`Box a, b) -> show_product a ^ " -> " ^ show b
    | `Arrow(a, b) -> show_product a ^ " => " ^ show b
    | tp -> show_product tp
  and show_product: tp -> string = function
    | `Product (_::_ as tps) -> String.concat ", " (List.map show_atom tps)
    | tp -> show_atom tp
  and show_atom: tp -> string = function
    | #base as b -> Base.show b
    | `Product [] -> "()"
    | `Sum [] -> "<void>"
    | `Set tp -> "{" ^ show tp ^ "}"
    | `Box tp -> "!" ^ show_atom tp
    | `Name n -> Var.show n
    | tp -> "(" ^ show tp ^ ")"

  let bool: tp = `Bool
  let int: tp = `Int
  let str: tp = `Str
  let unit: tp = `Product []

  (* TODO: type equality, join, meet. *)
  let rec discrete: tp -> bool = function
    | `Str | `Box _ -> true
    | `Arrow (_,b) -> discrete b
    | `Product ts -> List.for_all discrete ts
    | `Sum cs -> List.for_all (fun (_,tp) -> discrete tp) cs
    | `Bool | `Int | `Name _ | `Set _ -> false
end


(* ---------- patterns ----------*)
type lit = [ `Bool of bool | `Int of int | `Str of string ]
type pat =
  [ lit
  | `Wild | `Var of var
  | `Box of pat | `Tuple of pat list | `Tag of tag * pat ]

module Lit = struct
  let show: lit -> string = function
    | `Bool true -> "true" | `Bool false -> "false"
    | `Int n -> Printf.sprintf "%d" n
    | `Str s -> Printf.sprintf "%S" s
end

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


(* ---------- expressions & declarations ---------- *)
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
  | `MkSet of 'a list
  (* Eliminations *)
  | `Unbox of 'a
  | `App of 'a * 'a
  | `For of 'a comp list * 'a
  (* (if M then N else O) is parsed as (case M of true -> N | false -> O) *)
  | `Case of 'a * (pat * 'a) list ]

(* NB. An equirecursive type! *)
type 'a exp = 'a * 'a exp expF
type expr = loc exp


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
      | `The(t,e) -> f e |> map (fun x -> `The (t, x))
      | `Prim s -> pure (`Prim s)
      | `Lub es -> forEach es f |> map (fun x -> `Lub x)
      | `Fix (x,e) -> f e |> map (fun e -> `Fix (x,e))
      | `Let (ds, e) -> forEach ds (DeclSeq.traverse f) ** f e
                        |> map (fun(ds,e) -> `Let(ds,e))
      (* introductions *)
      | `Box e -> f e |> map (fun x -> `Box x)
      | `Lam(x,e) -> f e |> map (fun e -> `Lam (x, e))
      | `Tuple es -> forEach es f |> map (fun xs -> `Tuple xs)
      | `Tag(n,e) -> f e |> map (fun e -> `Tag(n,e))
      | `MkSet es -> forEach es f |> map (fun xs -> `MkSet xs)
      (* eliminations *)
      | `Unbox e -> f e |> map (fun x -> `Unbox x)
      | `App (e1, e2) -> f e1 ** f e2 |> map (fun (x,y) -> `App(x,y))
      | `For (cs, e) ->
         forEach cs (CompSeq.traverse f) ** f e
         |> map (fun (cs,e) -> `For(cs,e))
      | `Case (e, arms) ->
         f e ** forEach arms (fun(p,x) -> pure p ** f x)
         |> map (fun(e,arms) -> `Case(e,arms))
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
    | `MkSet es -> "{" ^ String.concat ", " (List.map show es) ^ "}"
    | _ -> "(" ^ show expr ^ ")"
end
