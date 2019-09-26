open Util open Types

(* For now, no typing contexts or variable usage/freeness information. *)
module type BASE = sig
  type tp
  type term
  val var: tp -> sym -> term
  val letIn: tp -> tp -> sym -> term -> term -> term
  val lam: tp -> tp -> sym -> term -> term
  val app: tp -> tp -> term -> term -> term
  val tuple: (tp * term) list -> term
  val proj: tp list -> int -> term -> term
  val letTuple: (tp * sym) list -> tp -> term -> term -> term
  val string: string -> term
  val bool: bool -> term
  val ifThenElse: tp -> term -> term -> term -> term
  val guard: tp semilat -> term -> term -> term
  (* set A [M0;...;Mn] = {M0,...,Mn} : {A} *)
  val set: eqtp -> term list -> term
  (* union A [M0;...;Mn] = M0 ∨ ... ∨ Mn : A *)
  val union: tp semilat -> term list -> term
  (* forIn A B x M N = for (x : A in M) do N : B *)
  val forIn: eqtp -> tp semilat -> sym -> term -> term -> term
  val fix: eqtp semilat -> term -> term
  val equals: eqtp -> term -> term -> term
end

module type MODAL = sig
  include BASE with type tp = modaltp
  (* var is now for monotone variables only *)
  val discvar: tp -> sym -> term (* for discrete variables *)
  val box: tp -> term -> term
  val letBox: tp -> tp -> sym -> term -> term -> term
end

module type SIMPLE = sig
  include BASE with type tp = rawtp
  val semifix: eqtp semilat -> term -> term
end

(* With the ability to explicitly flag certain terms as zero changes. *)
module type ZERO = sig
  include SIMPLE
  val zero: tp -> term -> term
end

module type BIDIR = sig
  type tp = modaltp
  type term
  type expr

  (* inferring exprs *)
  val asc: tp -> term -> expr
  val var: sym -> expr
  val app: expr -> term -> expr
  val proj: int -> expr -> expr
  val equals: expr -> expr -> expr

  (* checking terms *)
  val expr: expr -> term
  val letIn: sym -> expr -> term -> term
  val string: string -> term
  val bool: bool -> term
  val ifThenElse: term -> term -> term -> term
  val guard: term -> term -> term
  val lam: sym -> term -> term
  val tuple: term list -> term
  val letTuple: sym list -> expr -> term -> term
  val set: term list -> term
  val union: term list -> term
  val forIn: sym -> expr -> term -> term
  val box: term -> term
  val letBox: sym -> expr -> term -> term
  val fix: sym -> term -> term
end
