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


module S: sig
  type 'a t
  val empty: 'a t
  val add: 'a -> 'a t -> 'a t
  val single: 'a -> 'a t
  val union: 'a t -> 'a t -> 'a t
  val unions: 'a t list -> 'a t
  val minus: 'a t -> 'a t -> 'a t
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

  let rec minus a b = match a, b with
    | [], _ -> []
    | a, [] -> a
    | (x::xs), (y::ys) ->
       let i = Pervasives.compare x y in
       if i < 0 then x :: minus xs b
       else minus (if i = 0 then xs else a) ys

  let add x s = union [x] s
  let unions l = List.fold_left union empty l
  let flatMap s f = unions (List.map f s)
  let isEmpty = function [] -> true | _ -> false
  let isSingle = function [x] -> Some x | _ -> None
  let toList x = x
  let fromList l = List.sort_uniq Pervasives.compare l
end
type 'a set = 'a S.t


(* Semilattices as objects. Could equally well be records or (first-class)
 * modules. *)
type 'a sl =
  < union: 'a list -> 'a
  ; isEmpty: 'a -> bool
  (* Law: union [y; x] == union [y; minus x y]
   * (fun x y -> x) is a valid, if suboptimal, implementation. *)
  ; minus: 'a -> 'a -> 'a >

let empty (x: 'a sl): 'a = x#union []

let setL: 'a set sl = object
    method union = S.unions
    method isEmpty = S.isEmpty
    method minus = S.minus
  end

let pairL (f: 'a sl) (g: 'b sl): ('a * 'b) sl = object
    method union l = List.split l |> fun (x,y) -> (f#union x, g#union y)
    method isEmpty (x,y) = f#isEmpty x && g#isEmpty y
    method minus (x1,y1) (x2,y2) = f#minus x1 x2, g#minus y1 y2
  end

let setPairL (): ('a set * 'b set) sl = pairL setL setL

type 'a top = Top | Some of 'a

let topL (f: 'a sl): 'a top sl = object
    method union l = (??)
    method isEmpty = function Top -> false | Some x -> f#isEmpty x
    method minus x y = match x,y with
      | Top, y -> Top
      | x, Top -> Some (empty f)
      | Some x, Some y -> Some (f#minus x y)
  end


(* SYNTAX *)
type lat = Set | Bool
type exp = Var of sym
         | Fn of sym * exp
         | App of exp * exp
         | Set of exp list
         | Vee of lat * exp list
         | For of lat * sym * exp * exp

type 'a dnf = {imm: 'a; kids: (clause * 'a dnf) list}
and clause = For of sym * neut
and norm = Neut of neut
         | Fn of sym * norm
         | Bool of neut set top dnf
         | Set of (norm set * neut set) dnf
and neut = Var of sym
         | App of neut * norm

module Clauses = Map.Make(struct type t = clause let compare = Pervasives.compare end)


(* Sets as computations: church-encoded initial semilattices. *)
module type SET = sig
  type 'a t
  val empty: 'a sl -> 'a t
  val single: 'a sl -> 'a -> 'a t
  val union: 'a sl -> 'a t list -> 'a t
end

module Dnf = struct
  let single x = {imm = x; kids = []}
end

module LazyDnf: SET = struct
  type 'a t = 'a -> 'a delay
  and  'a delay = D of 'a * 'a t Clauses.t

  let empty lat used = D (lat#union [], Clauses.empty)
  let single lat elem used = D (lat#minus elem used, Clauses.empty)
  let union lat dnfs used =
    let f a = match a used with D(x,y) -> x,y in
    let imms, kids = List.map f dnfs |> List.split in
    let imm = lat#union imms in
    D (imm,
       (??))
end

type 'a setC = < run: 'b. 'b sl -> ('a -> 'b LazyDnf.t) -> 'b LazyDnf.t >

type 'a setI =
  < eval: 'a setC -> 'a dnf
  ; empty: 'a setC
  ; single: 'a -> 'a setC
  ; union: 'a setC list -> 'a setC
  >

let setC (lat: 'a sl): 'a setI = (??)

(* type 'a setC = < run: 'b. 'b sl -> ('a -> 'b dnf) -> 'b dnf >
 * 
 * let rec setC (type a) (lat: a sl) = object (self)
 *   method eval (s: a setC): a dnf = s#run lat Dnf.single
 * 
 *   method empty = object (_: a setC) method run latb f = Dnf.single (latb#union []) end
 *   method single (x: a) = object (_: a setC) method run latb f = f x end
 *   method union (l: a setC list): a setC = object
 *       (_: a setC)
 *       method run blat f = (??)
 *     end
 *   method fromList (xs: a list): a setC = self#union (List.map self#single xs)
 * end *)


(* NBE *)
type value
  = Neut of neut
  | Fn of string * (value -> value)
  | Set of (norm set * neut set) setC

let rec reify: value -> norm = function
  | Neut n -> Neut n
  | Fn (name,f) -> let x = Sym.gen name in Fn(x, reify (f (Neut (Var x))))
  | Set s -> Set ((setC (pairL setL setL))#eval s)

type env = value cx
let rec eval (term: exp) (env: env): value = match term with
  | Var x -> (try Cx.find x env
              with Not_found -> Neut (Var x))
  | Fn (x,body) -> Fn (x.name, fun v -> eval body (Cx.add x v env))
  | App (fnc,arg) ->
     (match eval fnc env with
      | Fn(x,f) -> f (eval arg env)
      | Neut f -> Neut (App (f, reify (eval arg env)))
      | _ -> fail "type error")
  | Set xs ->
     let elems = List.map (fun x -> eval x env) xs in
     (??)
  | Vee (lat, xs) ->
     let sets = List.map (fun x -> eval x env) xs in
     (??)
  | For (lat, x, set, body) ->
     (match eval set env with
      | Neut e -> (??)
      | Set c -> (??)
      | _ -> fail "type error")
