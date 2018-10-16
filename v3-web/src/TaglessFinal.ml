module TaglessFinal = struct

exception Todo let todo() = raise Todo
exception TypeError of string
exception Impossible

let typeError s = raise (TypeError s)

(* Symbols are strings annotated with unique identifiers. *)
type sym = {name: string; id: int}

(* Types. *)
type tp = Base | Prod of tp list | Fn of tp * tp
let subtype (a: tp) (b: tp) = a = b

let next_id = ref 0
let nextId() = let x = !next_id in next_id := x + 1; x
let gensym name () = {name = name; id = nextId()}

(* Contexts mapping variables to stuff. TODO: better representation. *)
type 'a cx = (sym * 'a) list
let get (cx: 'a cx) (x: sym): 'a = List.assoc x cx
let set (cx: 'a cx) (x: sym) (v: 'a): 'a cx = (x,v) :: cx


(* ===== LANGUAGE ALGEBRAS as ML MODULES (a la tagless final style) ===== *)
(* Bidirectionally-typed Datafun. *)
module type BIDI = sig
  type term
  type expr

  val expr: expr -> term
  val lam: sym -> term -> term
  val tuple: term list -> term

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
end

(* Explicitly typed, in "normal" form. *)
module type NORMAL = sig
  type term
  type expr

  val expr: tp -> expr -> term
  val lam: tp -> tp -> sym -> term -> term
  val tuple: (tp * term) list -> term

  val var: tp -> sym -> expr
  val app: tp -> tp -> expr -> term -> expr
  val proj: tp list -> int -> expr -> expr
end


(* ===== Normalisation by evaluation (intensional) =====
 * Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
 *)
module Simplify(N: NORMAL) = struct
  type value = Neut of N.expr
             | Func of string * (value -> value)
             | Tuple of value list

  let rec reify (tp: tp) (v: value): N.term = match v,tp with
    | Neut e, _ -> N.expr tp e
    | Tuple vs, Prod tps -> N.tuple (List.map2 (fun a v -> (a, reify a v)) tps vs)
    | Func(name,f), Fn(a,b) ->
       let x = gensym name () in
       N.lam a b x (reify b (f (Neut (N.var a x))))
    | Tuple _, _ | Func _, _ -> raise Impossible

  (* TODO: better environment representation *)
  type env = value cx
  type term = env -> value

  let var a x env = try get env x with Not_found -> Neut (N.var a x)
  let lam _ _ x m env = Func (x.name, (fun v -> m ((x,v)::env)))
  let tuple terms env = Tuple (List.map (fun (_,t) -> t env) terms)

  let app a b m n env = match m env with
    | Neut f -> Neut (N.app a b f (reify a (n env)))
    | Func(_,f) -> f (n env)
    | Tuple _ -> raise Impossible

  let proj tps i m env = match m env with
    | Neut e -> Neut (N.proj tps i e)
    | Tuple xs -> List.nth xs i
    | Func _ -> raise Impossible

  let norm tp (t: term): N.term = reify tp (t [])
end
module Nbe_: NORMAL -> TYPED = Simplify


(* A bidirectional type checker implements a bidirectionally-typed language
 * given an explicitly-typed one. *)
module Check(T: TYPED): BIDI
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
    | Fn(a,b) -> T.lam a b x (m (set cx x a) b)
    | _ -> typeError "lambda must be a function"

  let tuple (tms: term list) (cx: tp cx): tp -> T.term = function
    | Prod tps ->
       (try T.tuple (List.map2 (fun a m -> (a, m cx a)) tps tms)
        with Invalid_argument _ -> typeError "wrong tuple length")
    | _ -> typeError "tuple must be a product"

  (* ----- Synthesizing expressions ----- *)
  let asc a m cx = (a, m cx a)

  let var (x: sym) (cx: tp cx): tp * T.term =
    let tp = try get cx x with Not_found -> typeError "unbound variable"
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

end
