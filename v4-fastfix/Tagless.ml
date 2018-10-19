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
exception TypeError of string
exception Impossible

type order = EQ | LT | GT
let cmp x y = let i = Pervasives.compare x y in
              if i < 0 then LT else if i > 0 then GT else EQ

let typeError s = raise (TypeError s)

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
module Set: sig
  type 'a t
  val empty: 'a t
  val add: 'a -> 'a t -> 'a t
  val single: 'a -> 'a t
  val union: 'a t -> 'a t -> 'a t
  val flat_map: 'a t -> ('a -> 'b t) -> 'b t
  val is_empty: 'a t -> bool
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
  let rec flat_map s f = List.fold_left union empty (List.map f s)
  let is_empty = function [] -> true | _ -> false
  let to_list x = x
  let from_list l = List.sort_uniq Pervasives.compare l
end
type 'a set = 'a Set.t


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
  val union: term -> term -> term
  val forSet: sym -> expr -> term -> term

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
  val union: tp -> term -> term -> term
  val forSet: tp -> tp -> sym -> term -> term -> term
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
  val forSet: tp -> tp -> sym -> expr -> term -> term

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

  let set _ terms env = Set (Set.from_list (List.map (fun t -> t env) terms))
  let union _ m n env = Set (Set.union (asSet (m env)) (asSet (n env)))
  let forSet _ _ x expr body env =
    let f v = asSet (body (Cx.add x v env))
    in Set (Set.flat_map (expr env |> asSet) f)
end

module Interp : sig
  type value = Interp_.value
  type env = Interp_.env
  include NORMAL with type term = Interp_.term with type expr = Interp_.expr
end = Interp_


(* A simplification pass, based on intensional normalisation by evaluation.
 * Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
 *
 * Goal: eliminate all higher-order subterms, assuming our input term
 * a) has only first-order free variables (inputs)
 * b) has a first-order type (output)
 *)
module Simplify_(N: NORMAL) = struct
  type value = Expr of N.expr
             | Func of string * (value -> value)
             | Tuple of value list
             (* 1. We never need to store a set of Funcs, b/c the type system
              *    (should) disallow it.
              * 2. uh-oh, how do we compare N.exprs? eh, if Pervasives.compare
              *    says they're equal, then we can probably treat them as equal.
              *
              * `vals` are elements; `exprs` are expressions we need to union
              * together. *)
             | Set of { vals: value set
                      ; exprs: N.expr set }
             | ForSet of tp * sym * N.expr * value

  let rec reify (tp: tp) (v: value): N.term = match v,tp with
    | Expr e, _ -> N.expr tp e
    | ForSet (a,x,e,body), b -> N.forSet a b x e (reify b body)
    | Tuple vs, Prod tps -> N.tuple (List.map2 (fun a v -> (a, reify a v)) tps vs)
    | Set v, SetOf a ->
       let valset = N.set a (Set.to_list v.vals |> List.map (reify a)) in
       if Set.is_empty v.exprs then valset
       else Set.to_list v.exprs
            |> List.map (N.expr (SetOf a))
            |> List.fold_left (N.union a) valset
    | Func(name,f), Fn(a,b) ->
       let x = Sym.gen name in
       N.lam a b x (reify b (f (Expr (N.var a x))))
    | (Tuple _|Func _|Set _), _ -> raise Impossible

  type env = value cx
  type term = env -> value

  let var a x env = try Cx.find x env with Not_found -> Expr (N.var a x)
  let letBind _ _ x expr body env = body (Cx.add x (expr env) env)

  (* FIXME: If forSet were allowed at any semilattice type, it could
   * generate functions and products, couldn't it? ARGH! *)
  let lam _ _ x m env = Func (x.name, (fun v -> m (Cx.add x v env)))
  let app a b m n env = match m env with
    | Expr f -> Expr (N.app a b f (reify a (n env)))
    | Func(_,f) -> f (n env)
    | _ -> raise Impossible

  let tuple terms env = Tuple (List.map (fun (_,t) -> t env) terms)
  let proj tps i m env = match m env with
    | Expr e -> Expr (N.proj tps i e)
    | Tuple xs -> List.nth xs i
    | _ -> raise Impossible

  let set _ tms env = Set { vals = List.map (fun m -> m env) tms |> Set.from_list;
                            exprs = Set.empty }
  let union _ m n env = match m env, n env with
    | Set x, Set y -> Set { vals = Set.union x.vals y.vals
                          ; exprs = Set.union x.exprs y.exprs }
    | Expr e, Set s | Set s, Expr e -> Set { s with exprs = Set.add e s.exprs }
    | Expr x, Expr y -> Set { vals = Set.empty; exprs = Set.from_list [x;y] }
    (* TODO: handle forSet! *)
    | ForSet (a,x,e,body), huh -> (??)
    | _ -> raise Impossible
  let forSet (a: tp) (b: tp) (x: sym) (expr: term) (body: term) (env: env): value =
    (* ah, shit. *)
    match expr env with
    | Expr e -> (??)
    | Set s -> (??)
    | ForSet _ -> (??)
    | _ -> raise Impossible

  let norm tp (t: term): N.term = reify tp (t Cx.empty)
end

module Simplify(N: NORMAL): sig
  type value = Simplify_(N).value
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

  let lam (x: sym) (m: term) (cx: tp cx): tp -> T.term = function
    | Fn(a,b) -> T.lam a b x (m (Cx.add x a cx) b)
    | _ -> typeError "lambda must be a function"

  let tuple (tms: term list) (cx: tp cx): tp -> T.term = function
    | Prod tps ->
       (try T.tuple (List.map2 (fun a m -> (a, m cx a)) tps tms)
        with Invalid_argument _ -> typeError "wrong tuple length")
    | _ -> typeError "tuple must be a product"

  let letBind (x: sym) (expr: expr) (body: term) (cx: tp cx) (b: tp): T.term =
    let a, ex = expr cx in T.letBind a b x ex (body (Cx.add x a cx) b)

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
  (* Check -> Simplify -> Interp *)
  module Simple = Simplify(Interp)
  module Check = Bidi(Simple)
  include Check

  type value = Interp.value

  let eval term cx tp env = Simple.norm tp (term cx tp) env
  let evalExpr (expr: expr) (cx: tp cx) (env: value cx): tp * value =
    let tp, simple = expr cx in
    tp, Simple.norm tp simple env

  (* Conveniences *)
  let x = Sym.gen "x" and y = Sym.gen "y" and z = Sym.gen "z"

  (* \x. x *)
  let ex1 = (lam x (expr (var x)));;
  let runex1 () = eval ex1 Cx.empty (Fn (Bool,Bool)) Cx.empty

  (* \x. (snd x, fst x) *)
  let swap = lam x (tuple [expr (proj 1 (var x)); expr (proj 0 (var x))])
  let runswap (a, b) =
    match eval swap Cx.empty (Fn (Prod [Bool;Bool], Prod [Bool;Bool])) Cx.empty with
    | Func f -> f (Tuple [Bool a; Bool b])
    | _ -> raise Impossible
end

(* end *)
