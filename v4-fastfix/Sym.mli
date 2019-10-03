type t
val compare: t -> t -> int
(* to_string is injective. *)
val to_string: t -> string
val name: t -> string
val d: t -> t
(* name (fresh x) = name (intern x) = x *)
val fresh: string -> t          (* makes a new one every time *)
val intern: string -> t
