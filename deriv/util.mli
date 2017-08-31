module type FUNCTOR = sig 
  type 'a t 
  val map : ('a -> 'b) -> 'a t -> 'b t 
end

module type MONAD = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type MONOIDAL = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val unit : unit -> unit t
  val ( ** ) : 'a t -> 'b t -> ('a * 'b) t
end

module type IDIOM = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val unit : unit -> unit t
  val ( ** ) : 'a t -> 'b t -> ('a * 'b) t
  val return : 'a -> 'a t
  val app : ('a -> 'b) t -> 'a t -> 'b t
end

module type SEQ = sig
  type 'a t
  val pair : 'a t * 'b t -> ('a * 'b) t
  val option : 'a t option -> 'a option t
  val result : ('a t, 'b) result -> ('a, 'b) result t
  val list : 'a t list -> 'a list t
end

module MkIdiom :
  functor (M : MONOIDAL) -> (IDIOM with type 'a t = 'a M.t)

module Monoidal :
  functor (M : MONAD) -> (IDIOM with type 'a t = 'a M.t)

module Seq :
  functor (A : IDIOM) -> (SEQ with type 'a t := 'a A.t)

module Pair :
  sig
    type ('a, 'b) t = 'a * 'b
    val fst : 'a * 'b -> 'a
    val snd : 'a * 'b -> 'b
    val map : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
    val pair : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
    val swap : 'a * 'b -> 'b * 'a
    val assoc : 'a * ('b * 'c) -> ('a * 'b) * 'c
    val assoc' : ('a * 'b) * 'c -> 'a * ('b * 'c)
    val unit : 'a * unit -> 'a
    val unit' : unit * 'a -> 'a
  end

module Result : sig
  type ('a, 'b) t = ('a, 'b) result
  val ok : 'a -> ('a, 'b) t
  val error : 'a -> ('b, 'a) t
  val result : ('a -> 'b) -> ('c -> 'b) -> ('a, 'c) t -> 'b
  val map : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) t -> ('b, 'd) t
  val return : 'a -> ('a, 'b) t
  val ( >>= ) : ('a, 'b) t -> ('a -> ('c, 'b) t) -> ('c, 'b) t
end

module Option : sig
  type 'a t = 'a option
  val some : 'a -> 'a t 
  val none : 'a t
  val option : ('a -> 'b) -> 'b -> 'a t -> 'b
  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val unit : unit -> unit t
  val ( ** ) : 'a t -> 'b t -> ('a * 'b) t
  val app : ('a -> 'b) t -> 'a t -> 'b t
end

module Fn : sig
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val id : 'a -> 'a
  val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val ( @ ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
  val map : ('a -> 'b) -> ('c -> 'd) -> ('b -> 'c) -> 'a -> 'd
end
