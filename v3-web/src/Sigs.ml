type 'a monoid = {empty: 'a; append: 'a -> 'a -> 'a}
module type MONOID = sig type t val monoid: t monoid end

module type FUNCTOR = sig
  type 'a t
  val map: ('a -> 'b) -> 'a t -> 'b t
end

(* Signatures often come in two varities:
 * 1. minimal, eg. IDIOMATIC, MONADIC, TRAVERSABLE
 * 2. batteries-included, eg. IDIOM, MONAD, TRAVERSE
 *
 * In general, prefer the batteries-included version. Util.ml provides functors
 * that turn minimal modules into batteries-included ones.
 *)


(* Idioms / applicatives / monoidal functors *)
module type IDIOMATIC = sig
  include FUNCTOR
  val pure: 'a -> 'a t
  val ( ** ): 'a t -> 'b t -> ('a * 'b) t
end

module type IDIOM = sig
  include IDIOMATIC
  (* val apply: ('a -> 'b) t -> 'a t -> 'b t *)
  (* val pair: 'a t * 'b t -> ('a * 'b) t *)
  (* val option: 'a t option -> 'a option t *)
  (* val result: ('a t, 'b) result -> ('a, 'b) result t *)
  val list: 'a t list -> 'a list t
  (* val forEach: 'a list -> ('a -> 'b t) -> 'b list t *)
  (* val (>>): 'a t -> 'b t -> 'b t *)
  (* val (<*\): 'a t -> 'b t -> 'a t *)
  val (=>): 'a t -> ('a -> 'b) -> 'b t
  (* should go in Functor, but whatever. *)
  (* val ($): ('a -> 'b) -> 'a t -> 'b t *)

  (* val onPair: ('a1 -> 'a2 t) -> ('b1 -> 'b2 t) -> 'a1 * 'b1 -> ('a2 * 'b2) t *)
  (* val onFst: ('a1 -> 'a2 t) -> 'a1 * 'b -> ('a2 * 'b) t *)
  (* val onSnd: ('b1 -> 'b2 t) -> 'a * 'b1 -> ('a * 'b2) t *)
end


(* Monads *)
module type MONADIC = sig
  type 'a t
  val pure: 'a -> 'a t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
end

module type MONAD = sig
  include MONADIC
  include IDIOM with type 'a t := 'a t
  val concat: 'a t t -> 'a t
end
