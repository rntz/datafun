(* Feature list:
 * - DONE: functions, tuples, let-bindings
 * - TODO: equality & inequality tests
 * - TODO finite sets
 * - TODO non-monotone functions OR modes?
 * - TODO booleans
 * - TODO subtyping
 * - TODO structural sum types
 * - TODO pattern-matching
 * - TODO semilattice types
 * - TODO fixed points
 *)

(* module TaglessFinal = struct *)

exception Todo let todo() = raise Todo
exception Impossible
exception TypeError of string
let typeError s = raise (TypeError s)

type order = EQ | LT | GT
let cmp x y = let i = Pervasives.compare x y in
              if i < 0 then LT else if i > 0 then GT else EQ

(* Symbols are strings annotated with unique identifiers. *)
type sym = {name: string; id: int}
module Sym = struct
  type t = sym
  let compare = Pervasives.compare
  let next_id = ref 0
  let nextId () = let x = !next_id in next_id := x + 1; x
  let gen name = {name = name; id = nextId()}
end

(* Types. *)
type tp = Bool | Prod of tp list | Fn of tp * tp | SetOf of tp
let subtype (a: tp) (b: tp) = a = b

(* Contexts mapping variables to stuff. *)
module Cx = Map.Make(Sym)
type 'a cx = 'a Cx.t


(* Sets, represented as sorted lists. This makes them work polymorphically
 * for any type for which Pervasives.compare works. *)
module ListSet: sig
  type 'a t
  val empty: 'a t
  val add: 'a -> 'a t -> 'a t
  val single: 'a -> 'a t
  val union: 'a t -> 'a t -> 'a t
  val unions: 'a t list -> 'a t
  val flat_map: 'a t -> ('a -> 'b t) -> 'b t
  val is_empty: 'a t -> bool
  val is_single: 'a t -> 'a option
  val to_list: 'a t -> 'a list
  val from_list: 'a list -> 'a t
end = struct
  type 'a t = 'a list
  let empty = []
  let single x = [x]
  let rec union a b = match a, b with
    | rest, [] | [], rest -> rest
    | (x::xs), (y::ys) -> match cmp x y with
                          | EQ -> x :: union xs ys
                          | LT -> x :: union xs b
                          | GT -> y :: union ys a
  let add x s = union [x] s
  let unions l = List.fold_left union empty l
  let flat_map s f = unions (List.map f s)
  let is_empty = function [] -> true | _ -> false
  let is_single = function [x] -> Some x | _ -> None
  let to_list x = x
  let from_list l = List.sort_uniq Pervasives.compare l
end
type 'a set = 'a ListSet.t


(* ===== LANGUAGE ALGEBRAS as ML MODULES (a la tagless final style) ===== *)
(* Bidirectionally-typed Datafun. *)
module type BIDI = sig
  type term
  type expr

  val expr: expr -> term
  val lam: sym -> term -> term
  val tuple: term list -> term
  val letBind: sym -> expr -> term -> term
  (* sets *)
  val set: term list -> term
  (* TODO: union: term list -> term *)
  val union: term -> term -> term
  val forIn: sym -> expr -> term -> term

  val asc: tp -> term -> expr
  val var: sym -> expr
  val app: expr -> term -> expr
  val proj: int -> expr -> expr
end

(* Explicitly typed. *)
module type TYPED = sig
  type term
  val var: tp -> sym -> term
  val lam: tp -> tp -> sym -> term -> term
  val app: tp -> tp -> term -> term -> term
  val tuple: (tp * term) list -> term
  val proj: tp list -> int -> term -> term
  val letBind: tp -> tp -> sym -> term -> term -> term
  val set: tp -> term list -> term
  (* tp is tp of result expression, not element type. *)
  val union: tp -> term -> term -> term
  (* first type is type of elements of iterated-over set.
   * second type is result type of whole computation.
   * currently this is always of form (SetOf b). *)
  val forIn: tp -> tp -> sym -> term -> term -> term
end

(* Explicitly typed, in "normal" form. *)
module type NORMAL = sig
  type term
  type expr

  val expr: tp -> expr -> term
  val lam: tp -> tp -> sym -> term -> term
  val tuple: (tp * term) list -> term
  val set: tp -> term list -> term
  val union: tp -> term -> term -> term
  val forIn: tp -> tp -> sym -> expr -> term -> term

  val var: tp -> sym -> expr
  val app: tp -> tp -> expr -> term -> expr
  val proj: tp list -> int -> expr -> expr
end


(* An evaluator for things in normal form. *)
module Interp_ = struct
  type value =
    | Bool of bool
    | Func of (value -> value)
    | Tuple of value list
    | Set of value set

  let asBool = function Bool b -> b | _ -> raise Impossible
  let asFunc = function Func f -> f | _ -> raise Impossible
  let asTuple = function Tuple ts -> ts | _ -> raise Impossible
  let asSet = function Set x -> x | _ -> raise Impossible

  type env = value cx
  type term = env -> value
  type expr = env -> value

  let expr _ (x: expr): term = x
  let var _ = Cx.find

  let lam _ _ x body env = Func (fun v -> body (Cx.add x v env))
  let app _ _ fnc arg env = asFunc (fnc env) (arg env)

  let tuple terms env = Tuple (List.map (fun (_,tm) -> tm env) terms)
  let proj _ i e env = List.nth (e env |> asTuple) i

  let set _ terms env = Set (ListSet.from_list (List.map (fun t -> t env) terms))
  let union _ m n env = Set (ListSet.union (asSet (m env)) (asSet (n env)))
  let forIn _ _ x expr body env =
    let f v = asSet (body (Cx.add x v env))
    in Set (ListSet.flat_map (expr env |> asSet) f)
end

module Interp : sig
  type value = Interp_.value
  type env = Interp_.env
  include NORMAL with type term = Interp_.term with type expr = Interp_.expr
end = Interp_


(* A printer for things in normal form. *)
module Display: NORMAL
       with type term = int -> string
        and type expr = int -> string
= struct
  type term = int -> string
  type expr = term
  let comma_sep (f: 'a -> string) : 'a list -> string = function
    | [] -> ""
    | [x] -> f x
    | x::xs -> f x ^ List.fold_right (fun x rest -> ", " ^ f x ^ rest) xs ""

  let pIf cond x = if cond then "(" ^ x ^ ")" else x

  (* TODO: this code is almost certainly wrong about precedence *)
  let expr _ e = e
  let lam _ _ x e p = pIf (p > 0) ("fn " ^ x.name ^ " => " ^ e 0)
  let tuple ms p = pIf (p >= 1) (comma_sep (fun m -> snd m 1) ms)
  let set _ ms p = "{" ^ comma_sep (fun x -> x 1) ms ^ "}"
  let union _ m n p = pIf (p > 1) (m 1 ^ " or " ^ n 1)
  let forIn _ _ x expr body p =
    pIf (p > 0) ("for " ^ x.name ^ " in " ^ expr 1 ^ " do " ^ body 0)
  let var _ x _ = x.name
  let app _ _ fnc arg p = pIf (p >= 2) (fnc 2 ^ " " ^ arg 1)
  let proj _ i expr p = pIf (p >= 2) ("pi " ^ string_of_int i ^ " " ^ expr 1)
end


module Hashcons(N: NORMAL) = struct
  type 'a wrap = {hash: int; ptr: 'a}
  type term = N.term wrap
  type expr = N.expr wrap
  module T = struct type t = term let hash x = x.hash let equal = (==) end
  module E = struct type t = expr let hash x = x.hash let equal = (==) end
end

(* TODO: make a functor that takes a NORMAL lang to one with equality &
   comparison on exprs. We can then use this in Simplify. The comparison should
   be pretty shallow, just enough to de-duplicate obvious things, and bottom out
   to physical equality for complex cases. *)


(* A simplification pass, based on intensional normalisation by evaluation.
 * Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
 *
 * Goal: eliminate all higher-order subterms, assuming our input term
 * a) has only first-order free variables (inputs)
 * b) has a first-order type (output)
 *)

module Simplify_(N: NORMAL) = struct
  module type VAL = sig
    type t
    val reify: tp -> t -> N.term
    val expr: N.expr -> t
    val func: string -> (t -> t) -> t
    val tuple: t list -> t
    val set: tp -> t list -> t
    val app: tp -> tp -> t -> t -> t
    val proj: tp list -> int -> t -> t
    val union: tp -> t -> t -> t
    val forIn: tp -> tp -> string -> t -> (t -> t) -> t
  end
  module rec V : VAL = struct
    (* TODO: Can I see value as another language, and tagless-final encode it?
     * the purpose of values, more or less, is to be reified. *)
    type t = Expr of N.expr
           | Func of string * (t -> t)
           | Tuple of t list
           (* `vals` are elements; `sets` are expressions we need to union
            * together. Invariant: `sets` contains no `Set` values. *)
           | Set of { elts: t set; sets: t set }
           | For of tp * string * N.expr * (t -> t)

    (* shit, I need a total order. fuck. Okay, thne I probably want to go to a
       hash-consed syntactic representation after simplification. *)
    module S = ListSet

    let expr x = Expr x
    let func s f = Func (s,f)
    let tuple xs = Tuple xs

    let rec reify (tp: tp) (v: t): N.term = match v,tp with
      | Expr e, _ -> N.expr tp e
      | Tuple vs, Prod tps -> N.tuple (List.map2 (fun a v -> (a, reify a v)) tps vs)
      | Set v, SetOf a ->
         let elts = N.set a (S.to_list v.elts |> List.map (reify a)) in
         if S.is_empty v.sets then elts
         else S.to_list v.sets |> List.map (reify tp)
              |> List.fold_left (N.union a) elts
      | For (a,name,e,body), _ ->
         let x = Sym.gen name in
         N.forIn a tp x e (reify tp (body (Expr (N.var a x))))
      | Func(name,f), Fn(a,b) ->
         let x = Sym.gen name in
         N.lam a b x (reify b (f (Expr (N.var a x))))
      | (Tuple _|Func _|Set _), _ -> raise Impossible

    (* FIXME: If forIn were allowed at any semilattice type, it could
     * generate functions and products, couldn't it? ARGH! *)
    let app (a: tp) (b: tp): t -> t -> t = function
      | Expr e -> fun arg -> Expr (N.app a b e (reify a arg))
      | Func (_,f) -> f
      | _ -> raise Impossible

    let proj (tps: tp list) (i: int): t -> t = function
      | Expr e -> Expr (N.proj tps i e)
      | Tuple xs -> List.nth xs i
      | _ -> raise Impossible

    (* Sets *)
    let asSet: t -> t set * t set = function
      | Set s -> s.elts, s.sets
      | (Expr _|For _) as e -> S.empty, S.single e
      | _ -> raise Impossible

    let mkSet (elts: t set) (sets: t set): t =
      match S.is_empty elts, S.is_single sets with
      | true, Some v -> v
      | _ -> Set { elts; sets }

    let set (_: tp) (xs: t list) = Set { elts = S.from_list xs; sets = S.empty }
    let union (_: tp) (x: t) (y: t): t =
      let xelts, xsets = asSet x and yelts, ysets = asSet y in
      mkSet (S.union xelts yelts) (S.union xsets ysets)
    let rec forIn (a: tp) (tp: tp) (x: string) (set: t) (body: t -> t): t =
      let elts, sets = asSet set in
      let runOnElt (v: t): t set * t set = asSet (body v) in
      let runOnSet: t -> t = function
        | Expr e -> For (a, x, e, body)
        (* Commuting conversion:
         * (for x in (for y in M do N) do O)
         * --> (for y in M do for x in N do O) *)
        | For (c, y, m, n) -> For (c, y, m, fun v -> forIn a tp x (n v) body)
        | Set _ | _ -> raise Impossible in
      let elt_elts, elt_sets = S.to_list elts |> List.map runOnElt |> List.split in
      let set_sets = S.to_list sets |> List.map runOnSet |> S.from_list in
      mkSet (S.unions elt_elts) (S.unions (set_sets :: elt_sets))
  end

  type value = V.t
  type env = value cx
  type term = env -> value

  let reify = V.reify
  let norm tp (t: term): N.term = reify tp (t Cx.empty)

  let var a x env = try Cx.find x env with Not_found -> V.expr (N.var a x)
  let letBind _ _ x expr body env = body (Cx.add x (expr env) env)

  let lam _ _ x m env = V.func x.name (fun v -> m (Cx.add x v env))
  let app a b m n env = V.app a b (m env) (n env)

  let tuple terms env = V.tuple (List.map (fun (_,t) -> t env) terms)
  let proj tps i m env = V.proj tps i (m env)

  let set a tms env = V.set a (List.map (fun m -> m env) tms)
  let union a m n env = V.union a (m env) (n env)
  let forIn a b x expr body env = V.forIn a b x.name (expr env)
                                    (fun v -> body (Cx.add x v env))
end

module Simplify(N: NORMAL): sig
  type value
  type env = value cx
  include TYPED with type term = env -> value
  val reify: tp -> value -> N.term
  val norm: tp -> term -> N.term
end = Simplify_(N)


(* A bidirectional type checker implements a bidirectionally-typed language
 * given an explicitly-typed one. *)
module Bidi(T: TYPED): BIDI
        with type term = tp cx -> tp -> T.term
        with type expr = tp cx -> tp * T.term
= struct
  type term = tp cx -> tp -> T.term
  type expr = tp cx -> tp * T.term

  (* ----- Checking terms ----- *)
  let expr e cx expected =
    let (inferred, term) = e cx in
    if subtype inferred expected then term
    else typeError "not a subtype"

  let letBind (x: sym) (expr: expr) (body: term) (cx: tp cx) (b: tp): T.term =
    let a, ex = expr cx in T.letBind a b x ex (body (Cx.add x a cx) b)

  let lam (x: sym) (m: term) (cx: tp cx): tp -> T.term = function
    | Fn(a,b) -> T.lam a b x (m (Cx.add x a cx) b)
    | _ -> typeError "lambda must be a function"

  let tuple (tms: term list) (cx: tp cx): tp -> T.term = function
    | Prod tps ->
       (try T.tuple (List.map2 (fun a m -> (a, m cx a)) tps tms)
        with Invalid_argument _ -> typeError "wrong tuple length")
    | _ -> typeError "tuple must be a product"

  let set (tms: term list) (cx: tp cx): tp -> T.term = function
    | SetOf a -> T.set a (List.map (fun m -> m cx a) tms)
    | _ -> typeError "set literal must have set type"

  let union (m: term) (n: term) (cx: tp cx): tp -> T.term = function
    | SetOf _ as tp -> T.union tp (m cx tp) (n cx tp)
    | _ -> typeError "union at non-set type"

  let forIn (x: sym) (e: expr) (body: term) (cx: tp cx): tp -> T.term = function
    | SetOf _ as tp ->
       let a, expr = e cx in
       T.forIn a tp x expr (body (Cx.add x a cx) tp)
    | _ -> typeError "for-expression at non-set type"

  (* ----- Synthesizing expressions ----- *)
  let asc a m cx = (a, m cx a)

  let var (x: sym) (cx: tp cx): tp * T.term =
    let tp = try Cx.find x cx with Not_found -> typeError "unbound variable"
    in tp, T.var tp x

  let app (fnc: expr) (arg: term) (cx: tp cx): tp * T.term =
    match fnc cx with
    | Fn(a,b), fx -> let ax = arg cx a in b, T.app a b fx ax
    | _ -> typeError "applying a non-function"

  let proj (i: int) (e: expr) (cx: tp cx): tp * T.term =
    match e cx with
    | Prod tps, ex -> (try List.nth tps i, T.proj tps i ex
                       with Failure _ -> typeError "bad projection index")
    | _ -> typeError "projection from non-tuple"
end


(* Putting it all together *)
module Lang = struct
  (* Check -> Simplify -> Display/Interp *)
  module Simple = Simplify(Display)
  module Check = Bidi(Simple)
  open Interp_                  (* for Interp.value constructors *)
  include Check

  type value = Interp.value

  let eval term cx tp env = Simple.norm tp (term cx tp) env
  let evalExpr expr cx env =
    let tp, simple = expr cx in
    tp, Simple.norm tp simple env

  (* Conveniences *)
  let x = Sym.gen "x" and y = Sym.gen "y" and z = Sym.gen "z"

  (* \x. x *)
  let ex1 = (lam x (expr (var x)));;
  let runex1 () = eval ex1 Cx.empty (Fn (Bool,Bool)) 0
  (* let runex1 () = eval ex1 Cx.empty (Fn (Bool,Bool)) Cx.empty *)

  (* \x. (snd x, fst x) *)
  let swap = lam x (tuple [expr (proj 1 (var x)); expr (proj 0 (var x))])
  let runswap () = eval swap Cx.empty (Fn (Prod [Bool;Bool], Prod [Bool;Bool])) 0
  (* let runswap (a, b) =
   *   match eval swap Cx.empty (Fn (Prod [Bool;Bool], Prod [Bool;Bool])) Cx.empty with
   *   | Func f -> f (Tuple [Bool a; Bool b])
   *   | _ -> raise Impossible *)

  (* \x. {x,x} *)
  let ex3 = lam x (set [expr (var x); expr (var x)])
  let runex3 () = eval ex3 Cx.empty (Fn (Bool, SetOf Bool)) 0

  (* \x. \y. {x,y} *)
  (* Huh, this one is erroring with "compare: functional value".
   * Can I get a backtrace? *)
  let ex4 = lam x (lam y (set [expr (var x); expr (var y)]))
  let runex4 () = eval ex4 Cx.empty (Fn (Bool, Fn (Bool, SetOf Bool))) 0

  (* \x. x union x *)
  let ex5 = (lam x (union (expr (var x)) (expr (var x))))
  let runex5 () = eval ex5 Cx.empty (Fn (SetOf Bool, SetOf Bool)) 0
end

(* this bugs out *)
(* shit, of _course_! terms in the language after Simplification are functions,
 * because I'm in tagless-final style! *)
let _ = Lang.(Simple.set Bool [Simple.var Bool x; Simple.var Bool x]) Cx.empty;;

(* end *)
