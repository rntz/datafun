type 'a seq

(* Optimizes the internal representation; worst case O(n).
 * Mostly useful if you plan on using the sequence non-linearly.
 *)
val force: 'a seq -> 'a seq

(* Miscellanea. *)
val size: 'a seq -> int
val null: 'a seq -> bool

(* Constructing sequences *)
val mkEmpty: unit -> 'a seq
val cons: 'a -> 'a seq -> 'a seq
val snoc: 'a seq -> 'a -> 'a seq
val append: 'a seq -> 'a seq -> 'a seq
val concat: 'a seq seq -> 'a seq
val concat_list: 'a seq list -> 'a seq
val concat_array: 'a seq array -> 'a seq

(* Transforming & destroying sequences *)
val map: ('a -> 'b) -> 'a seq -> 'b seq
val fold_left: ('a -> 'b -> 'a) -> 'a -> 'b seq -> 'a
val fold_right: ('b -> 'a -> 'a) -> 'b seq -> 'a -> 'a

(* Conversions *)
val of_array_unsafe: 'a array -> 'a seq
val of_array: 'a array -> 'a seq
val of_list: 'a list -> 'a seq

val to_array_unsafe: 'a seq -> 'a array
val to_array: 'a seq -> 'a array
val to_list: 'a seq -> 'a list
