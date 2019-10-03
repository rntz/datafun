type t
val compare: t -> t -> int
val name: t -> string
val to_string: t -> string
val d: t -> t
val fresh: string -> t          (* makes a new one every time *)
val intern: string -> t
