type t
val finish: t -> string
val string: string -> t
val int: int -> t
val (^): t -> t -> t
val concat: t -> t list -> t
