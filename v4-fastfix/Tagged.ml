(* Feature list:
 - functions, tuples, let-bindings, finite sets
 - TODO if/then/else & when/then
 - TODO equality & inequality tests
 - TODO fixed points
 - TODO strings, or some base type I can compute with
 - TODO subtyping
 - TODO structural sum types
 - TODO pattern-matching
 - TODO semilattice types other than sets
 - TODO: monotonicity types!! (modes? modal subtyping? arrow annotations?)
 *)

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


(* ===== Normalised intermediate language ===== *)
module IL = struct
  (* NB. should have type annotations where necessary.
   * Might need them on variable bindings for derivative transform. *)
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
       match List.map reify (S.toList v.elts), List.map reify (S.toList v.sets) with
       | elts, [] -> `Set elts
       | [], sets -> `Vee (LSet, sets)
       | elts, sets -> `Vee (LSet, `Set elts :: sets)

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


(* ===== Pretty-printing ===== *)
module Show = struct
  open IL
  open Format

  let paren (out: formatter) (cxPrec: int) (opPrec: int) f =
    if cxPrec <= opPrec then f out else (fprintf out "(@[%t@])" f)

  let sepBy sep (f: formatter -> 'a -> unit): formatter -> 'a list -> unit =
    pp_print_list ~pp_sep:(fun out _ -> fprintf out sep) f

  let rec tp (prec: int) (out: formatter): tp -> unit = function
    | Bool -> fprintf out "bool"
    | Set a -> fprintf out "{@[%a@]}" (tp 0) a
    | Prod ts -> paren out prec 1 (fun f -> sepBy ",@ " (tp 2) f ts)
    | Fn (a,b) -> paren out prec 0 (fun f -> fprintf f "%a -> %a" (tp 1) a (tp 0) b)

  (* Dealing with variables is annoying. *)
  module SS = Set.Make(struct type t = string let compare = Pervasives.compare end)
  type cx = {used: SS.t; vars: string Cx.t}
  let empty: cx = {used = SS.empty; vars = Cx.empty}

  (* Generates a fresh variable name, returning it & updated context. *)
  let bind x cx =
    let return n = n, {used = SS.add n cx.used; vars = Cx.add x n cx.vars} in
    let rec propose i name = if SS.mem name cx.used then loop i else return name
    and loop (i:int) = propose (i+1) (sprintf "%s%x" x.name i) in
    propose 0 x.name

  (* Precedence (higher binds tighter):
   * 0 Fn, For
   * 1 Vee, Tuple
   * 9 App, Pi *)
  let rec neut cx prec out (e: neut) = norm cx prec out (e :> norm)
  and norm (cx: cx) (prec: int) (out: formatter) (term: norm): unit =
    let printf: 'a. ('a,formatter,unit) format -> 'a = fun x -> fprintf out x in
    let sepBy sep prec = sepBy sep (norm cx prec) in
    let par = paren out prec in
    match term with
    | `Var x -> (try printf "%s" (Cx.find x cx.vars)
                 with Not_found -> printf "%s.%d" x.name x.id)
    | `App(fnc,arg) ->
       par 9 (fun _ -> printf "%a@ %a" (neut cx 9) fnc (norm cx 10) arg)
    | `Fn(x,e) ->
       let name, ecx = bind x cx in
       par 0 (fun _ -> printf "λ%s. @[%a@]" name (norm ecx 0) e)
    | `Pi(i,e) ->
       let pi = match i with 0 -> "fst" | 1 -> "snd" | i -> sprintf "pi_%i" i in
       par 9 (fun _ -> printf "%s@ %a" pi (neut cx 10) e)
    | `Tuple ts -> par 1 (fun _ -> sepBy ",@," 2 out ts)
    | `Set ts -> printf "{@[%a@]}" (sepBy ",@," 2) ts
    | `Vee(_,[]) -> printf "empty"
    | `Vee(_,[t]) -> par 1 (fun _ -> printf "@[or %a@]" (norm cx 2) t)
    | `Vee(_,ts) -> par 1 (fun _ -> printf "@[%a@]" (sepBy "@ or " 2) ts)
    | `For(_,x,e,t) ->
       let name, tcx = bind x cx in
       match t with
       | `Set[t] -> printf "{@[%a@]@ | %s in @[%a@]}" (norm tcx 2) t name (neut cx 2) e
       | t -> par 0 (fun _ -> printf "for %s in @[%a@] do@ %a"
                                name (neut cx 1) e (norm tcx 0) t)
end

module Print = struct
  open Format
  let tp ?(out = std_formatter) ?(prec = 0) = fprintf out "@[%a@]\n" (Show.tp prec)
  let norm ?(out = std_formatter) ?(cx = Show.empty) ?(prec = 0) =
    fprintf out "@[%a@]\n" (Show.norm cx prec)
end


(* ===== Surface language & translation to IL ===== *)
module Lang = struct
  open IL

  (* Surface language *)
  type ('t,'e) exprF
    = [ `Var of sym | `The of tp * 't
      | `App of 'e * 't | `Pi of int * 'e ]
  type ('t,'e) termF
    = [ ('t,'e) exprF
      | `Let of sym * 'e * 't
      | `Fn of sym * 't | `Tuple of 't list
      | `Set of 't list | `Vee of 't list | `For of sym * 'e * 't ]

  type term = (term,expr) termF
  and  expr = (term,expr) exprF

  (* For now, subtyping is equality. *)
  let subtp got expect =
    if got = expect then ()
    else typeError (Format.asprintf "cannot treat %a as %a"
                      (Show.tp 10) got (Show.tp 10) expect)

  let rec check (term: term) (expect: tp) (cx: tp cx): sem =
    match term, expect with
    | #expr as e, _ -> let got, sem = infer e cx in subtp got expect; sem
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
                 with Not_found -> typeError ("unbound variable: " ^ x.name))
    | `The(tp,term) -> tp, check term tp cx
    | `App(fnc,arg) ->
       (match infer fnc cx with
        | Fn(a,b), fncx -> b, app fncx (check arg a cx)
        | _ -> typeError "applying non-function")
    | `Pi(i,e) ->
       (try match infer e cx with Prod tps, sem -> List.nth tps i, pi i sem
                                | _ -> typeError "projection from non-tuple"
        with Invalid_argument _ -> typeError "wrong tuple length")
end


(* ===== Tests ===== *)
(* TODO: MOAR tests. *)
module Test = struct
  open Lang

  let x = Sym.gen "x" let y = Sym.gen "y" let z = Sym.gen "z"
  let vx = `Var x     let vy = `Var y     let vz = `Var z

  let b2b = Fn(Bool,Bool)
  let s2s = Fn(Set Bool, Set Bool)
  let s2b = Fn(Set Bool, Bool)
  let b2s = Fn(Bool, Set Bool)
  let ss2ss = Fn(Set (Set Bool), Set (Set Bool))

  (* ===== Identity functions =====
   * All of these could in principle normalise to (λx.x). *)
  (* THE VANILLA        λx.x *)
  let idT: term = `Fn(x, vx)
  let idN = IL.norm (check idT b2b Cx.empty)

  (* THE INDIRECTOR     λx.(λy.y)x *)
  let idkT: term = `Fn(x, `App(`The(b2b,`Fn(y, vy)), vx))
  let idkN = IL.norm (check idT b2b Cx.empty)

  (* THE UNIONIST       λx. x ∪ x *)
  let idsetT: term = `Fn(x, `Vee [vx; vx])
  let idsetN = IL.norm (check idsetT s2s Cx.empty)

  (* THE EXTENSION      λx.λy.xy
   * We don't η-shorten, so this normalizes to itself. *)
  let idetaT: term = `Fn(x, `Fn(y, `App(vx,vy)))
  let idetaN = IL.norm (check idetaT (Fn(b2b,b2b)) Cx.empty)

  (* THE THESAURUS      λx. let y = x in y *)
  let idletT: term = `Fn(x, `Let(y, vx, vy))
  let idletN = IL.norm (check idletT b2b Cx.empty)

  (* THE CHROMOSOMES    λx.fst(x,x) *)
  let idupT: term = `Fn(x, `Pi(0, `The (Prod [Bool; Bool], `Tuple [vx; vx])))
  let idupN = IL.norm (check idupT b2b Cx.empty)

  (* THE ITERATOR       λx. {y | y ∈ x}
   * unfortunately, we do not yet normalise this to (λx.x).
   * I should look into this if it comes up in real programs. *)
  let idforT: term = `Fn(x, `For (y, vx, `Set [vy]))
  let idforN = IL.norm (check idforT s2s Cx.empty)

  (* THE RUSSIAN DOLL    λx. {y | y ∈ {z | z ∈ x}}
   * this normalizes to λ.x {z | z ∈ x}, which is great, but I don't understand
   * why, even though I wrote the damn code. *)
  let idnestT: term =
    `Fn(x, `For(y, `The(Set Bool, `For(z, vx, `Set [vz])), `Set [vy]))
  let idnestN = IL.norm (check idnestT s2s Cx.empty)

  (* THE SOVIET DOLL   λx. {{z | z ∈ y} | y ∈ x} *)
  let idnest2T: term = `Fn(x, `For(y, vx, `For(z, vy, `Set [`Set [vz]])))
  let idnest2N = IL.norm (check idnest2T ss2ss Cx.empty)

  (* THE SHAGGY DOG     λx. for y in x ∪ x do snd(y, {y, (λz.z) y})
   * Presently normalizes to λx. {y | y in x}. *)
  let idigressT: term =
    `Fn(x, `For(y, `The(Set Bool, `Vee [vx;vx]),
                `Pi(1, `The(Prod [Bool; Set Bool],
                            `Tuple [vy; `Set [vy; `App(`The(b2b, `Fn (z, vz)), vy)]]))))
  let idigressN = IL.norm (check idigressT s2s Cx.empty)

  (* ===== Non-identity funcs ===== *)
  let singleT: term = `Fn(x, `Set [vx])
  let singleN = IL.norm (check singleT b2s Cx.empty)

  (* λxy. (x,y) *)
  let pairT: term = `Fn(x, `Fn(y, `Tuple [vx;vy]))
  let pairN = IL.norm (check pairT (Fn(Bool, Fn(Bool, Prod[Bool;Bool]))) Cx.empty)

  (* λxy. empty or x or (y or (or x)) *)
  let unionT: term = `Fn(x, `Fn(y, `Vee [`Vee []; vx; `Vee [vy; `Vee [vx]]]))
  let unionN = IL.norm (check unionT (Fn(Set Bool, Fn(Set Bool, Set Bool))) Cx.empty)
end
