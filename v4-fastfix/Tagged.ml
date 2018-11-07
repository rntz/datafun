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

(* Finite maps, represented as sorted lists. *)
module M: sig
  type ('k,'v) t
  val empty: ('k,'v) t
  val single: 'k -> 'v -> ('k,'v) t
  val add: 'k -> 'v -> ('k,'v) t -> ('k,'v) t
  val map: ('v1 -> 'v2 option) -> ('k,'v1) t -> ('k,'v2) t
  val union: ('v -> 'v -> 'v) -> ('k,'v) t -> ('k,'v) t -> ('k,'v) t
  val unions: ('v list -> 'v) -> ('k,'v) t list -> ('k,'v) t
  val find: 'k -> ('k,'v) t -> 'v
  val isEmpty: ('k,'v) t -> bool
  val toList: ('k,'v) t -> ('k * 'v) list
  (* TODO: figure out semantics in case of duplicate keys. *)
  val fromList: ('k * 'v) list -> ('k,'v) t
end = struct
  type ('k,'v) t = ('k * 'v) list
  let empty = []
  let single k v = [(k,v)]
  let map f = fail "TODO: M.map"
  let union f x y = fail "TODO: M.union"
  let unions f sets = fail "TODO: M.unions"
  let add k v xs = union (fun _ v1 v2 -> Some v1) [(k,v)] xs
  let find = List.assoc
  let isEmpty = function [] -> true | _ -> false
  let toList x = x
  let fromList x = fail "TODO: fromList"
end
type ('a,'b) map = ('a,'b) M.t


(* ===== Syntax ===== *)
module Lang = struct
  (* Surface language *)
  type ('t,'e) exprF
    = [ `Var of sym | `The of tp * 't | `Bool of bool
      | `App of 'e * 't | `Pi of int * 'e ]
  type ('t,'e) termF
    = [ ('t,'e) exprF
      | `Let of sym * 'e * 't
      | `Fn of sym * 't | `Tuple of 't list
      | `Set of 't list
      | `When of 't * 't | `Vee of 't list | `For of sym * 'e * 't ]

  type term = (term,expr) termF
  and  expr = (term,expr) exprF

  (* Normalised intermediate language *)
  type neut = Var of sym | App of neut * norm | Pi of int * neut
  and loop = For of sym * neut | When of neut
  and 'a dnf = {imm: 'a; kids: (loop, 'a dnf) map}
  and norm =
    | Neut of neut
    | Fn of sym * norm
    | Tuple of norm list
    (* I think I really want an abstract data structure parameterized by
     * a notion of _subsumption_, or perhaps _static difference_. *)
    | Bool of (neut set option) dnf
    (* `Set(elts, subsets) *)
    | Set of (norm set * neut set) dnf

end

module type SL = sig
  type t
  val isEmpty: t -> bool
  val empty: t
  val union: t -> t -> t
  val unions: t list -> t
end

module Dnf(X: SL) = struct
  open Lang
  type t = X.t dnf

  let isEmpty (x: t) = X.isEmpty x.imm && M.isEmpty x.kids
  let maybe (x: t): t option = if isEmpty x then None else Some x

  let empty = {imm = X.empty; kids = M.empty}
  let single (x: X.t): t = {imm = x; kids = M.empty}

  let rec map (f: 'a -> X.t) (x: 'a dnf): t =
    { imm = f x.imm; kids = M.map (mapMaybe f) x.kids }
  and mapMaybe f x = maybe (map f x)

  let rec union (x: t) (y: t): t =
    { imm = X.union x.imm y.imm; kids = M.union union x.kids y.kids }

  let rec unions (xs: t list): t =
    List.map (fun x -> x.imm, x.kids) xs |> List.split
    |> fun (imms, kids) -> {imm = X.unions imms; kids = M.unions unions kids}

  let rec bind (x: 'a dnf) (f: 'a -> t): t =
    let visit (x: 'a dnf): t option = maybe (bind x f) in
    let {imm; kids} = f x.imm in
    {imm; kids = M.union union kids (M.map visit x.kids)}
end


(* ===== Pretty-printing ===== *)
module Show = struct
  open Lang
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
   * 0 Fn, For, When
   * 1 Vee, Tuple
   * 9 App, Pi *)
  (* let rec neut cx prec out (e: neut) = norm cx prec out (e :> norm)
   * and norm (cx: cx) (prec: int) (out: formatter) (term: norm): unit =
   *   let printf: 'a. ('a,formatter,unit) format -> 'a = fun x -> fprintf out x in
   *   let sepBy sep prec = sepBy sep (norm cx prec) in
   *   let par = paren out prec in
   *   match term with
   *   | `Var x -> (try printf "%s" (Cx.find x cx.vars)
   *                with Not_found -> printf "%s.%d" x.name x.id)
   *   | `Bool b -> printf (if b then "yes" else "no")
   *   | `App(fnc,arg) ->
   *      par 9 (fun _ -> printf "%a@ %a" (neut cx 9) fnc (norm cx 10) arg)
   *   | `Fn(x,e) ->
   *      let name, ecx = bind x cx in
   *      par 0 (fun _ -> printf "λ%s. @[%a@]" name (norm ecx 0) e)
   *   | `Pi(i,e) ->
   *      let pi = match i with 0 -> "fst" | 1 -> "snd" | i -> sprintf "pi_%i" i in
   *      par 9 (fun _ -> printf "%s@ %a" pi (neut cx 10) e)
   *   | `Tuple ts -> par 1 (fun _ -> sepBy ",@," 2 out ts)
   *   | `Set ts -> printf "{@[%a@]}" (sepBy ",@," 2) ts
   *   | `When(_,cnd,body) ->
   *      par 0 (fun _ -> printf "when @[%a@] do@ %a" (neut cx 1) cnd (norm cx 0) body)
   *   | `Vee(_,[]) -> printf "empty"
   *   | `Vee(_,[t]) -> par 1 (fun _ -> printf "@[or %a@]" (norm cx 2) t)
   *   | `Vee(_,ts) -> par 1 (fun _ -> printf "@[%a@]" (sepBy "@ or " 2) ts)
   *   | `For(_,x,e,t) ->
   *      let name, tcx = bind x cx in
   *      match t with
   *      | `Set[t] -> printf "{@[%a@]@ | %s in @[%a@]}" (norm tcx 2) t name (neut cx 2) e
   *      | t -> par 0 (fun _ -> printf "for %s in @[%a@] do@ %a"
   *                               name (neut cx 1) e (norm tcx 0) t) *)
end

module Print = struct
  open Format
  let tp ?(out = std_formatter) ?(prec = 0) = fprintf out "@[%a@]\n" (Show.tp prec)
  (* let norm ?(out = std_formatter) ?(cx = Show.empty) ?(prec = 0) =
   *   fprintf out "@[%a@]\n" (Show.norm cx prec) *)
end


(* ===== Semantic "values" used for NBE ===== *)
module type VALUE = sig
  type t
  val reify: t -> Lang.norm
  val var: sym -> t
  val bool: bool -> t
  val fn: string -> (t -> t) -> t
  val tuple: t list -> t
  val app: t -> t -> t
  val pi: int -> t -> t
  val set: t list -> t
  val vee: semilat -> t list -> t
  val whenDo: semilat -> t -> t -> t
  val forIn: semilat -> string -> t -> (t -> t) -> t
end

module Value = struct
  open Lang
  (* Instead of defining values positively, what if I defined them negatively,
     by what I can do to them? This is probably best investigated in either a
     dependently-typed or untyped host language. *)
  type t = Neut of neut
         | Fn of string * (t -> t)
         | Tuple of t list
         (* I'm not convinced here. *)
         | Bool of neut set option dnf
         (* (t set) or (norm set)? *)
         | Set of (t set * neut set) dnf
  type value = t

  module BoolSL = struct
    type t = neut set option
    let isEmpty = function Some s -> S.isEmpty s | _ -> false
    let empty = Some S.empty
    let union x y = match x,y with
      | None, _ | _, None -> None
      | Some x, Some y -> Some (S.union x y)
    let unions = List.fold_left union empty
  end
  module SetSL(X: sig type t end) = struct
    type t = X.t set * neut set
    let isEmpty (x,y) = S.isEmpty x && S.isEmpty y
    let empty = S.empty, S.empty
    let union (xn,xe) (yn,ye) = S.union xn yn, S.union xe ye
    let unions l = List.split l |> fun (ns,es) -> S.unions ns, S.unions es
  end
  module BoolDnf = Dnf(BoolSL)
  module SetDnf = Dnf(SetSL(struct type t = value end))
  module NormSetDnf = Dnf(SetSL(struct type t = norm end))

  let var x = Neut (Var x)
  let bool b = Bool {imm = if b then None else Some S.empty; kids = M.empty}
  let fn s f = Fn(s,f)
  let tuple ts = Tuple ts

  let rec reify: t -> norm = function
    | Neut x -> Neut x
    | Bool b -> Bool b
    | Fn(name,f) -> let x = Sym.gen name in Fn (x, reify (f (var x)))
    | Tuple xs -> Tuple (List.map reify xs)
    | Set s -> Set (NormSetDnf.map (fun (x,es) -> (??), es) s)
    (* | Set (elts, disj) ->
     *    Set (S.toList elts |> List.map reify |> S.fromList, disj) *)

  (* TODO: once funcs are semilattice types, we could apply a For or Vee! *)
  let app: t -> t -> t = function
    | Neut e -> fun x -> Neut (App (e, reify x))
    | Fn(x,f) -> f
    | _ -> fail "app"

  (* TODO: once tuples are semilattice types, could pi a For or Vee! *)
  let pi (i: int): t -> t = function
    | Neut e -> Neut (Pi (i,e))
    | Tuple xs -> List.nth xs i
    | _ -> fail "pi"

  (* Set normalisation. The hard bit. *)
  (* let asSet: t -> t set * disj = function
   *   | Set(xs,d) ->  xs, d
   *   | Neut x -> S.empty, S.single ([], x)
   *   | _ -> fail "asSet"
   * 
   * let set xs = Set (S.fromList xs, S.empty)
   * 
   * let vee (how: semilat) (xs: t list): t = match how with
   *   | LSet -> let elts, sets = List.map asSet xs |> List.split in
   *             Set (S.unions elts, S.unions sets)
   *   | LBool -> fail "todo: vee for booleans"
   *   | LProd _ -> fail "todo: vee for products" *)

  (* TODO: need to handle if/then/else, vee, when, and for at boolean type:

       when (when M do N) do P         -->  when M do when N do P
       when (for x in M do N) do P     -->  for x in M do when N do P
       when (if M then N else P) do Q  -->  if M then (when N do Q) else (when P do Q)?

       TODO: should I rewrite
           when M do (N or P)  -->  (when M do N) or (when N do P)
       or vice-versa?
   *)
  (* let whenDo (how: semilat) (cond: t) (body: t): t = match cond, body with
   *   | Bool None, body -> body
   *   | Bool (Some conds), body -> (??)
   *   | Neut e, Set (elts, disj) -> (??)
   *   | Neut _, Bool _ -> fail "todo: whenDo for boolean body"
   *   | _ -> fail "whenDo" *)

  (* let rec forIn (how: semilat) (x: string) (set: t) (body: t -> t): t =
   *   (??)
   *   (\* let elts, sets = asSet set in
   *    * let onElt (v: t): t set * t set = asSet (body v) in
   *    * let onSet: t -> t = function
   *    *   | Neut e -> For (how, x, e, body)
   *    *   (\\* Commuting conversion:
   *    *        for x in (for y in M do N) do O  -->  for y in M do for x in N do O
   *    *    *\\)
   *    *   | For (LSet, y, inner_set, inner_body) ->
   *    *      For (how, y, inner_set, fun v -> forIn how x (inner_body v) body)
   *    *   | Set _ | _ -> fail "forIn/onSet" in
   *    * let elt_elts, elt_sets = S.toList elts |> List.map onElt |> List.split in
   *    * let set_sets = S.toList sets |> List.map onSet |> S.fromList in
   *    * toSet (S.unions elt_elts) (S.unions (set_sets :: elt_sets)) *\) *)

end


(* NBE, using our abstract values. *)
module NBE = struct
  open Lang
  module A = Value
  type value = Value.t
  type env = value cx
  type sem = env -> value
  type t = sem

  let norm (x: sem): norm = A.reify (x Cx.empty)

  let var (x: sym) (e: env): value = try Cx.find x e with Not_found -> A.var x
  let bool (b: bool) (e: env): value = A.bool b
  let tuple (xs: sem list) (e: env): value = A.tuple (List.map ((|>) e) xs)
  let pi (i: int) (x: sem) (e: env) = A.pi i (x e)
  let fn (x: sym) (body: sem) (e: env): value = A.fn x.name (fun v -> body (Cx.add x v e))
  let app (f: sem) (a: sem) (e: env) = A.app (f e) (a e) (* S combinator! *)
  let letBind (x: sym) (e: sem) (body: sem) (env: env): value = body (Cx.add x (e env) env)
  let set (xs: sem list) (e: env): value = A.set (List.map ((|>) e) xs)
  let whenDo how cond body env = A.whenDo how (cond env) (body env)
  let vee (how: semilat) (xs: sem list) (e: env): value = A.vee how (List.map ((|>) e) xs)
  let forIn (how: semilat) (x: sym) (expr: sem) (body: sem) (env: env): value =
    A.forIn how x.name (expr env) (fun v -> body (Cx.add x v env))
end


(* ===== Typechecking & translation to IL ===== *)
module Check = struct
  open Lang
  open NBE

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
    | `When(cnd, body), tp -> whenDo (semilat tp) (check cnd Bool cx) (check body tp cx)
    | `Vee terms, tp -> vee (semilat tp) (List.map (fun t -> check t tp cx) terms)
    | `For(x,e,body), tp ->
       (match infer e cx with
        | Set a, ex -> forIn (semilat tp) x ex (check body tp (Cx.add x a cx))
        | _ -> typeError "comprehending over non-set")
    | (`Fn _|`Tuple _|`Set _), _ -> typeError "type mismatch"

  and infer (e: expr) (cx: tp cx): tp * sem = match e with
    | `Bool b -> Bool, bool b
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
  let check = Check.check
  let norm = NBE.norm

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
  let idN = norm (check idT b2b Cx.empty)

  (* THE INDIRECTOR     λx.(λy.y)x *)
  let idkT: term = `Fn(x, `App(`The(b2b,`Fn(y, vy)), vx))
  let idkN = norm (check idT b2b Cx.empty)

  (* THE UNIONIST       λx. x ∪ x *)
  let idsetT: term = `Fn(x, `Vee [vx; vx])
  let idsetN = norm (check idsetT s2s Cx.empty)

  (* THE YES-MAN        λx. when yes do x *)
  let idwhenT: term = `Fn(x, `When(`Bool true, vx))
  let idwhenN = norm (check idwhenT s2s Cx.empty)

  (* THE EXTENSION      λx.λy.xy
   * We don't η-shorten, so this normalizes to itself. *)
  let idetaT: term = `Fn(x, `Fn(y, `App(vx,vy)))
  let idetaN = norm (check idetaT (Fn(b2b,b2b)) Cx.empty)

  (* THE THESAURUS      λx. let y = x in y *)
  let idletT: term = `Fn(x, `Let(y, vx, vy))
  let idletN = norm (check idletT b2b Cx.empty)

  (* THE CHROMOSOMES    λx.fst(x,x) *)
  let idupT: term = `Fn(x, `Pi(0, `The (Prod [Bool; Bool], `Tuple [vx; vx])))
  let idupN = norm (check idupT b2b Cx.empty)

  (* THE ITERATOR       λx. {y | y ∈ x}
   * unfortunately, we do not yet normalise this to (λx.x).
   * I should look into this if it comes up in real programs. *)
  let idforT: term = `Fn(x, `For (y, vx, `Set [vy]))
  let idforN = norm (check idforT s2s Cx.empty)

  (* THE RUSSIAN DOLL    λx. {y | y ∈ {z | z ∈ x}}
   * this normalizes to λ.x {z | z ∈ x}, which is great, but I don't understand
   * why, even though I wrote the damn code. *)
  let idnestT: term =
    `Fn(x, `For(y, `The(Set Bool, `For(z, vx, `Set [vz])), `Set [vy]))
  let idnestN = norm (check idnestT s2s Cx.empty)

  (* THE SOVIET DOLL   λx. {{z | z ∈ y} | y ∈ x} *)
  let idnest2T: term = `Fn(x, `For(y, vx, `For(z, vy, `Set [`Set [vz]])))
  let idnest2N = norm (check idnest2T ss2ss Cx.empty)

  (* THE SHAGGY DOG     λx. for y in x ∪ x do snd(y, {y, (λz.z) y})
   * Presently normalizes to λx. {y | y in x}. *)
  let idigressT: term =
    `Fn(x, `For(y, `The(Set Bool, `Vee [vx;vx]),
                `Pi(1, `The(Prod [Bool; Set Bool],
                            `Tuple [vy; `Set [vy; `App(`The(b2b, `Fn (z, vz)), vy)]]))))
  let idigressN = norm (check idigressT s2s Cx.empty)

  (* ===== Non-identity funcs ===== *)
  let singleT: term = `Fn(x, `Set [vx])
  let singleN = norm (check singleT b2s Cx.empty)

  (* λx. when no do x ∪ x *)
  let whenfalseT: term = `Fn(x, `When(`Bool false, vx))
  let whenfalseN = norm (check whenfalseT s2s Cx.empty)

  (* λxy. (x,y) *)
  let pairT: term = `Fn(x, `Fn(y, `Tuple [vx;vy]))
  let pairN = norm (check pairT (Fn(Bool, Fn(Bool, Prod[Bool;Bool]))) Cx.empty)

  (* λxy. empty or x or (y or (or x)) *)
  let unionT: term = `Fn(x, `Fn(y, `Vee [`Vee []; vx; `Vee [vy; `Vee [vx]]]))
  let unionN = norm (check unionT (Fn(Set Bool, Fn(Set Bool, Set Bool))) Cx.empty)
end
