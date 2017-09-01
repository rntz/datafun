open Ast

type tone = Disc | Mono
type error = string * loc

type 'a t

val return : 'a -> 'a t 
val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t 
val map : ('a -> 'b) -> 'a t -> 'b t 

val gensym : var -> var t 
val fail : ('a, unit, string, 'b t) format4 -> 'a 
val setloc : loc -> unit t 

val into : exp expF -> exp t 
val out : exp -> exp expF t 

val lookup : string -> (tp * tone) t 
val with_hyp : string * tp * tone -> 'a t -> 'a t 
val hidemono  : 'a t -> 'a t 

module Seq : sig
  val pair : 'a t * 'b t -> ('a * 'b) t 
  val option : 'a t option -> 'a option t 
  val result : ('a t, 'b) result -> ('a,'b) result t 
  val list : 'a t list -> 'a list t
end 
                                                
