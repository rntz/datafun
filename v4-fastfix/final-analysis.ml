type ('a,'b) sum = L of 'a | R of 'b
type tp = Base | Fn of tp * tp

type sym = string
module Sym = struct type t = sym let compare = Pervasives.compare end

module Cx = struct include Map.Make(Sym) end
type 'a cx = 'a Cx.t

type term = Var of sym
          | Lam of sym * term
          | App of term * term
          | LetIn of sym * term * term
          | Empty of tp

module type LANG = sig
  type info
  type value
  val var: sym -> info -> value
  val lam: sym -> (info -> value) -> value
  val app: value -> value -> value
  val letIn: value -> (info -> value) -> value
  val empty: tp -> value
end

module Interpret(L: LANG) = struct
  let rec run (cx: L.info cx): term -> L.value = function
    | Empty tp -> L.empty tp
    | Var x -> L.var x (Cx.find x cx)
    | Lam (x,body) -> L.lam x (fun info -> run (Cx.add x info cx) body)
    | App (m,n) -> L.app (run cx m) (run cx n)
    | LetIn (x,expr,body) ->
       L.letIn (run cx expr) (fun info -> run (Cx.add x info cx) body)
end

module Subst(L: LANG): LANG
       with type info = (L.info, L.value) sum
       with type value = L.value
= struct
  type info = (L.info, L.value) sum
  type value = L.value
  let var x = function R v -> v | L info -> L.var x info
  let lam x body = L.lam x (fun info -> body (L info))
  let app = L.app
  let letIn expr body = body (R expr)
  let empty tp = L.empty tp
end

module IsEmpty(L: LANG): LANG
= struct
  type info = (L.info, tp) sum
  type value = (L.value, tp) sum
  let empty tp = R tp
  let var x = function R tp -> R tp | L info -> L (L.var x info)
  (* shit. I simply don't have the info I need! *)
  let lam (x: sym) (m: info -> value): value = (??)
  let app = (??)
  let letIn = (??)
end


(* Another approach. *)
module type LANG_BIND = sig
  type term
  type 'a bind                  (* does bind have to be an Applicative? *)
  val var: sym -> term bind     (* ?!?!?!?!?! *)
  val lam: sym -> term bind -> term
  val app: term -> term -> term
  val letIn: term -> term bind -> term
end

(* LANG2 is more general than LANG, somehow. *)
module Foo(X: LANG): LANG_BIND = struct
  include X
  type term = value
  type 'a bind = info -> 'a
end
