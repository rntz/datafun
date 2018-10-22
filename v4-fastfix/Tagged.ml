(* Feature list:
 - functions, tuples, let-bindings, finite sets
 - TODO fixed points
 - TODO equality & inequality tests
 - TODO strings, or some base type I can compute with
 - TODO if-then-else expressions
 - TODO subtyping
 - TODO structural sum types
 - TODO pattern-matching
 - TODO semilattice types other than sets
 - TODO: monotonicity types!! (modes? modal subtyping? arrow annotations?)
 *)

exception Todo let todo() = raise Todo
exception TypeError of string
exception Fail of string
let typeError s = raise (TypeError s)
let fail s = raise (Fail s)

(* Symbols are strings annotated with unique identifiers. *)
type sym = {name: string; id: int}
module Sym = struct
  type t = sym
  let compare = Pervasives.compare
  let next_id = ref 0
  let nextId () = let x = !next_id in next_id := x + 1; x
  let gen name = {name = name; id = nextId()}
end

(* Contexts mapping variables to stuff. *)
module Cx = Map.Make(Sym)
type 'a cx = 'a Cx.t

(* Types. *)
type tp = Bool | Fn of tp * tp | Prod of tp list | Set of tp
let subtype (a: tp) (b: tp) = a = b

(* Just enough information to know how to perform semilattice operations at
 * runtime. *)
type semilat = LBool | LSet | LProd of semilat list
let rec semilat: tp -> semilat = function
  | Set a -> LSet | Bool -> LBool
  | Prod tps -> LProd (List.map semilat tps)
  | _ -> typeError "not a semilattice type"


(* Sets, represented polymorphically as list sorted by Pervasives.compare. Not
   very efficient, but doesn't require module knot-tying contortions. *)
module S: sig
  type 'a t
  val empty: 'a t
  val add: 'a -> 'a t -> 'a t
  val single: 'a -> 'a t
  val union: 'a t -> 'a t -> 'a t
  val unions: 'a t list -> 'a t
  val flatMap: 'a t -> ('a -> 'b t) -> 'b t
  val isEmpty: 'a t -> bool
  val isSingle: 'a t -> 'a option
  val toList: 'a t -> 'a list
  val fromList: 'a list -> 'a t
end = struct
  type 'a t = 'a list
  let empty = []
  let single x = [x]
  let rec union a b = match a, b with
    | rest, [] | [], rest -> rest
    | (x::xs), (y::ys) ->
       let i = Pervasives.compare x y in
       if i = 0 then x :: union xs ys else
       if i < 0 then x :: union xs b
                else y :: union ys a
  let add x s = union [x] s
  let unions l = List.fold_left union empty l
  let flatMap s f = unions (List.map f s)
  let isEmpty = function [] -> true | _ -> false
  let isSingle = function [x] -> Some x | _ -> None
  let toList x = x
  let fromList l = List.sort_uniq Pervasives.compare l
end
type 'a set = 'a S.t


(* Normalised intermediate language. *)
module IL = struct
  (* NB. should have type annotations where necessary. *)
  type ('t,'e) neutF = [ `Var of sym | `App of 'e * 't | `Pi of int * 'e ]
  type ('t,'e) normF =
    [ ('t,'e) neutF | `Fn of sym * 't | `Tuple of 't list
    | `Set of 't list
    (* vee and for only need enough *)
    | `Vee of semilat * 't list | `For of semilat * sym * 'e * 't ]

  type norm = (norm,neut) normF
  and  neut = (norm,neut) neutF
  type value = Neut of neut
             | Fn of string * (value -> value) | Tuple of value list
             | Set of {elts: value set; sets: value set}
             | For of semilat * string * neut * (value -> value)
  type env = value cx
  type sem = env -> value

  let rec reify: value -> norm = function
    | Neut e -> (e :> norm)
    | Fn(name,f) -> let x = Sym.gen name in `Fn (x, reify (f (Neut (`Var x))))
    | Tuple xs -> `Tuple (List.map reify xs)
    | For (sl,name,expr,body) ->
       let x = Sym.gen name in `For (sl, x, expr, reify (body (Neut (`Var x))))
    | Set v ->
       let elts = `Set (S.toList v.elts |> List.map reify) in
       if S.isEmpty v.sets then elts
       else `Vee (LSet, elts :: List.map reify (S.toList v.sets))

  let norm (x: sem): norm = reify (x Cx.empty)

  module V = struct
    (* TODO: once funcs are semilattice types, we could apply a For or Vee! *)
    let app: value -> value -> value = function
      | Neut e -> fun x -> Neut (`App (e, reify x))
      | Fn(x,f) -> f
      | _ -> fail "app"

    (* TODO: once tuples are semilattice types, could pi a For or Vee! *)
    let pi (i: int): value -> value = function
      | Neut e -> Neut (`Pi (i,e))
      | Tuple xs -> List.nth xs i
      | _ -> fail "pi"

    (* Set normalisation. The hard bit. *)
    let asSet: value -> value set * value set = function
      | Set s -> s.elts, s.sets
      | (Neut _|For _) as e -> S.empty, S.single e
      | _ -> fail "asSet"

    let toSet (elts: value set) (sets: value set): value =
      match S.isEmpty elts, S.isSingle sets with
      | true, Some v -> v
      | _ -> Set {elts; sets}

    let set xs = Set {elts = S.fromList xs; sets = S.empty}

    let vee (how: semilat) (xs: value list): value = match how with
      | LSet -> let elts, sets = List.map asSet xs |> List.split in
                toSet (S.unions elts) (S.unions sets)
      | _ -> fail "todo: vee"

    let rec forIn (how: semilat) (x: string) (set: value) (body: value -> value): value =
      let elts, sets = asSet set in
      let onElt (v: value): value set * value set = asSet (body v) in
      let onSet: value -> value = function
        | Neut e -> For (how, x, e, body)
        (* Commuting conversion:
         * (for x in (for y in M do N) do O)
         * --> (for y in M do for x in N do O) *)
        | For (LSet, y, inner_set, inner_body) ->
           (* FIXME: double check this *)
           For (how, y, inner_set, fun v -> forIn how x (inner_body v) body)
        | Set _ | _ -> fail "forIn/onSet" in
      let elt_elts, elt_sets = S.toList elts |> List.map onElt |> List.split in
      let set_sets = S.toList sets |> List.map onSet |> S.fromList in
      toSet (S.unions elt_elts) (S.unions (set_sets :: elt_sets))
  end

  let var: sym -> env -> value = Cx.find
  let fn (x: sym) (body: sem) (e: env): value = Fn (x.name, fun v -> body (Cx.add x v e))
  let tuple (xs: sem list) (e: env): value = Tuple (List.map ((|>) e) xs)
  let letBind (x: sym) (e: sem) (body: sem) (env: env): value = body (Cx.add x (e env) env)
  let app (f: sem) (a: sem) (e: env) = V.app (f e) (a e) (* S combinator! *)
  let pi (i: int) (x: sem) (e: env) = V.pi i (x e)
  let set (xs: sem list) (e: env): value = V.set (List.map ((|>) e) xs)
  let vee (how: semilat) (xs: sem list) (e: env): value = V.vee how (List.map ((|>) e) xs)
  let forIn (how: semilat) (x: sym) (expr: sem) (body: sem) (env: env): value =
    V.forIn how x.name (expr env) (fun v -> body (Cx.add x v env))
end


(* Surface language & translation to IL. *)
module Lang = struct
  open IL

  (* Surface language *)
  type ('t,'e) exprF
    = [ `Var of sym | `Asc of tp * 't 
      | `App of 'e * 't | `Pi of int * 'e ]
  type ('t,'e) termF
    = [ ('t,'e) exprF
      | `Let of sym * 'e * 't
      | `Fn of sym * 't | `Tuple of 't list
      | `Set of 't list | `Vee of 't list | `For of sym * 'e * 't ]

  type term = (term,expr) termF
  and  expr = (term,expr) exprF

  let rec check (term: term) (expect: tp) (cx: tp cx): sem =
    match term, expect with
    | #expr as e, _ -> let got, sem = infer e cx in
                       if subtype got expect then sem
                       else typeError "subtype check failed"
    | `Let(x,e,body), bodytp ->
       let etp, ex = infer e cx in
       letBind x ex (check body bodytp (Cx.add x etp cx))
    | `Fn(x,body), Fn(a,b) -> fn x (check body b (Cx.add x a cx))
    | `Tuple terms, Prod tps ->
       tuple (try List.map2 (fun t a -> check t a cx) terms tps
              with Invalid_argument _ -> typeError "wrong tuple length")
    | `Set terms, Set a -> set (List.map (fun t -> check t a cx) terms)
    | `Vee terms, tp -> vee (semilat tp) (List.map (fun t -> check t tp cx) terms)
    | `For(x,e,body), tp ->
       (match infer e cx with
        | Set a, ex -> forIn (semilat tp) x ex (check body tp (Cx.add x a cx))
        | _ -> typeError "comprehending over non-set")
    | (`Fn _|`Tuple _|`Set _), _ -> typeError "type mismatch"

  and infer (e: expr) (cx: tp cx): tp * sem = match e with
    | `Var x -> (try Cx.find x cx, var x
                 with Not_found -> typeError "unbound variable")
    | `Asc(tp,term) -> tp, check term tp cx
    | `App(fnc,arg) ->
       (match infer fnc cx with
        | Fn(a,b), fncx -> b, app fncx (check arg a cx)
        | _ -> typeError "applying non-function")
    | `Pi(i,e) ->
       (try match infer e cx with Prod tps, sem -> List.nth tps i, pi i sem
                                | _ -> typeError "projection from non-tuple"
        with Invalid_argument _ -> typeError "wrong tuple length")
end


(* Tests. TODO: MOAR tests. *)
module Test = struct
  open Lang

  let x = Sym.gen "x" let y = Sym.gen "y" let z = Sym.gen "z"
  let vx = `Var x     let vy = `Var y     let vy = `Var z

  let b2b = Fn(Bool,Bool)
  let s2s = Fn(Set Bool, Set Bool)

  (* ===== Identity functions =====
   * All of these should normalize to (λx.x).
   * (λx.x)         THE VANILLA*)
  let idterm: term = `Fn(x, vx)
  let idnorm = IL.norm (check idterm b2b Cx.empty)

  (* λx.(λy.y)x     THE INDIRECTOR *)
  let id2term: term = `Fn(x, `App(`Asc(b2b,`Fn(y, vy)), vx))
  let id2norm = IL.norm (check idterm b2b Cx.empty)

  (* (\x. x ∪ x)    THE UNIONIST *)
  let idsetTerm: term = `Fn(x, `Vee [vx; vx])
  let idsetNorm = IL.norm (check idsetTerm s2s Cx.empty)

  (* λx.π₁(x,x)     THE TWINS *)
  let idprojTerm: term = `Fn(x, `Pi(0, `Asc (Prod [Bool; Bool], `Tuple [vx; vx])))
  let idprojNorm = IL.norm (check idprojTerm b2b Cx.empty)
end
