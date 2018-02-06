open Sigs
open Util

type loc = {start: Lexing.position; finish: Lexing.position}
type var = string
type tag = string
type prim = string
module Var = struct let show x = x end
module Tag = struct let show n = n end
module Prim = struct let show p = p end


(* ---------- types ---------- *)
type tone = Mono | Anti | Isos | Path
type base = Bool | Nat | Str
module Base = struct
  let show = function | Bool -> "bool" | Nat -> "nat" | Str -> "str"
end

type tp =
  | Name of var
  | Base of base
  | Set of tp
  | Box of tp
  | Arrow of tp * tp
  | Product of tp list
  (* TODO: use hashtable? *)
  | Sum of (tag * tp) list

module Type = struct
  type t = tp

  let rec show = function
    | Sum ctors ->
       let show_ctor (tag, tp) = match tp with
         | Product [] -> Tag.show tag
         | tp -> Tag.show tag ^ " " ^ show_unary tp
       in String.concat " | " (List.map show_ctor ctors)
    | tp -> show_arrow tp
  and show_arrow = function
    | Arrow(Box a, b) -> show_product a ^ " -> " ^ show b
    | Arrow(a, b) -> show_product a ^ " => " ^ show b
    | tp -> show_product tp
  and show_product = function
    | Product [] -> "()"
    | Product tps -> String.concat ", " (List.map show_unary tps)
    | tp -> show_unary tp
  and show_unary = function
    | Set tp -> "{" ^ show tp ^ "}"
    | Box tp -> "!" ^ show_unary tp
    | Base b -> Base.show b
    | tp -> "(" ^ show tp ^ ")"

  let bool = Base Bool
  let nat = Base Nat
  let str = Base Str
  let unit = Product []

  (* TODO: type equality, join, meet. *)
  let rec discrete = function
    | Base Str | Box _ -> true
    | Arrow (a,b) -> discrete b
    | Product ts -> List.for_all discrete ts
    | Sum cs -> List.for_all (fun (c,tp) -> discrete tp) cs
    | _ -> false
end


(* ---------- patterns ----------*)
type lit = LBool of bool | LNat of int | LStr of string
type pat =
  | PWild
  | PVar of var
  | PLit of lit
  | PBox of pat                 (* do we need this? *)
  | PTuple of pat list | PTag of tag * pat

module Lit = struct
  let show = function | LBool true -> "true" | LBool false -> "false"
                      | LNat n -> raise TODO
                      | LStr s -> raise TODO
end
module Pat = struct
  let rec show = function
    | PTuple ps -> String.concat ", " (List.map show_unary ps)
    | p -> show_unary p
  and show_unary = function
    | PTag (n,p) -> n ^ " " ^ show_unary p
    | PBox p -> "!" ^ show_unary p
    | p -> show_atomic p
  and show_atomic = function
    | PVar v -> Var.show v
    | PLit l -> Lit.show l
    | PWild -> "_"
    | p -> "(" ^ show p ^ ")"
end


(* ---------- expressions & declarations ---------- *)
type 'a comp = When of 'a | In of pat * 'a
type 'a decl =
  | Type of var * tp
  | Ascribe of var list * tp
  | Define of var * pat list * 'a
  | Decons of pat * 'a

type 'a expF =
  | Var of var
  | The of tp * 'a              (* type annotation *)
  | Lit of lit
  | Prim of prim                (* builtin functions *)
  | Lub of 'a list
  | Fix of var * 'a
  | Let of 'a decl list * 'a
  (* Introductions *)
  | Box of 'a
  | Lam of pat list * 'a
  | Tuple of 'a list | Tag of tag * 'a
  | MkSet of 'a list
  (* Eliminations *)
  | Unbox of 'a
  | App of 'a * 'a
  | For of 'a comp list * 'a
  (* (if M then N else O) is parsed as (case M of true -> N | false -> O) *)
  | Case of 'a * (pat * 'a) list

type 'a exp = E of 'a * 'a exp expF


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

module Decl = Traverse(struct
  type 'a t = 'a decl
  module Seq(M: IDIOM) = struct
    open M
    let traverse f = function
      | Type(x,t) -> pure (Type(x,t))
      | Ascribe(xs,t) -> pure (Ascribe(xs,t))
      | Define(x,args,body) -> map (fun body' -> Define(x, args, body')) (f body)
      | Decons(p,e) -> map (fun x -> Decons(p,x)) (f e)
  end
end)

module ExpT: TRAVERSABLE with type 'a t = 'a expF = struct
  type 'a t = 'a expF
  module Seq(M: IDIOM) = struct
    open M
    module DeclSeq = Decl.Seq(M)
    module CompSeq = Comp.Seq(M)

    (* I find myself wanting lenses. *)
    let traverse (f: 'a -> 'b M.t) = function
      | Var x -> pure (Var x)
      | The(t,e) -> f e |> map (fun x -> The (t, x))
      | Lit l -> pure (Lit l)
      | Prim s -> pure (Prim s)
      | Lub es -> forEach es f |> map (fun x -> Lub x)
      | Fix (x,e) -> f e |> map (fun e -> Fix (x,e))
      | Let (ds, e) -> forEach ds (DeclSeq.traverse f) ** f e
                       |> map (fun(ds,e) -> Let(ds,e))
      (* introductions *)
      | Box e -> f e |> map (fun x -> Box x)
      | Lam(x,e) -> f e |> map (fun e -> Lam (x, e))
      | Tuple es -> forEach es f |> map (fun xs -> Tuple xs)
      | Tag(n,e) -> f e |> map (fun e -> Tag(n,e))
      | MkSet es -> forEach es f |> map (fun xs -> MkSet xs)
      (* eliminations *)
      | Unbox e -> f e |> map (fun x -> Unbox x)
      | App (e1, e2) -> f e1 ** f e2 |> map (fun (x,y) -> App(x,y))
      | For (cs, e) ->
         forEach cs (CompSeq.traverse f) ** f e
         |> map (fun (cs,e) -> For(cs,e))
      | Case (e, arms) ->
         f e ** forEach arms (fun(p,x) -> pure p ** f x)
         |> map (fun(e,arms) -> Case(e,arms))
  end
end

module Exp = struct
  include Traverse(ExpT)

  let rec show (E(_, e) as expr) = match e with
    | The (a,x) -> "the " ^ Type.show_unary a ^ " " ^ show x
    | Fix (x,e) -> Var.show x ^ " as " ^ show e
    | Let (ds,e) ->
       let show_decl = function
         | Type (x,tp) -> "type " ^ Var.show x ^ " = " ^ Type.show tp
         | Ascribe (xs, tp) -> String.concat " " xs ^ " : " ^ Type.show tp
         | Define (x,ps,body) ->
            [Var.show x] @ List.map Pat.show_atomic ps @ ["="; show body]
            |> String.concat " "
         | Decons (p,e) -> Pat.show p ^ " = " ^ show e
       in "let " ^ String.concat " " (List.map show_decl ds) ^ " in " ^ show e
    (* introductions *)
    | Lam (ps, e) ->
       ["fn"] @ List.map Pat.show_atomic ps @ ["->"; show e]
       |> String.concat " "
    (* eliminations *)
    | For (cs, e) ->
       let show_comp = function
         | When e -> "when " ^ show_app e
         | In (p,e) -> Pat.show_unary p ^ " in " ^ show_app e
       in "for (" ^ String.concat ", " (List.map show_comp cs) ^ ") " ^ show e
    | Case (e, pes) ->
       let show_branch (p,e) = Pat.show p ^ " -> " ^ show_disj e
       in "case " ^ show_disj e ^ String.concat "| " (List.map show_branch pes)
    | _ -> show_disj expr
  and show_disj (E (_,e) as expr) = match e with
    | Tuple es -> List.map show_app es |> String.concat ", "
    | Lub (_::_ as es) -> List.map (fun x -> "or " ^ show_app x) es |> String.concat " "
    | _ -> show_app expr
  and show_app (E (_,e) as expr) = match e with
    | App (e1,e2) -> show_app e1 ^ show_atomic e2
    | Tag (n,e) -> Tag.show n ^ " " ^ show_atomic e
    | Box e -> "box " ^ show_atomic e
    | Unbox e -> "unbox " ^ show_atomic e
    | _ -> show_atomic expr
  and show_atomic (E (_,e) as expr) = match e with
    | Var x -> Var.show x
    | Lit l -> Lit.show l
    | Prim p -> Prim.show p
    | Lub [] -> "empty"
    | MkSet es -> "{" ^ String.concat ", " (List.map show es) ^ "}"
    | _ -> "(" ^ show expr ^ ")"
end
