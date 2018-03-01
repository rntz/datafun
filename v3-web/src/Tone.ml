type tone = [`Id | `Op | `Iso | `Path]

let show: tone -> string = function
  | `Id -> "id" | `Op -> "op" | `Iso -> "iso" | `Path -> "path"

(* TODO: factor out the repetition in meet, join, (<=) *)
let meet (a: tone) (b: tone): tone = match a, b with
  | `Iso, _ | _, `Iso | `Id, `Op | `Op, `Id -> `Iso
  | x, `Path | `Path, x -> x
  | `Id, `Id | `Op, `Op -> a

let join (a: tone) (b: tone): tone = match a, b with
  | _, `Path | `Path, _ | `Id, `Op | `Op, `Id -> `Path
  | `Iso, x | x, `Iso -> x
  | `Id, `Id | `Op, `Op -> a

let (<=) (a: tone) (b: tone): bool = match a,b with
  | `Iso, _ | _, `Path | `Id, `Id | `Op, `Op -> true
  | _, `Iso | `Path, _ | `Op, `Id | `Id, `Op -> false

(* Order of composition is postfix: A^(compose s t) == (A^s)^t *)
let compose (a: tone) (b: tone): tone = match a,b with
  | x, `Id | `Id, x -> x
  | `Op, `Op -> `Id
  | `Iso, _ | `Path, _ -> a   (* hi priority, must come first *)
  | _, `Iso | _, `Path -> b   (* lo priority, comes later *)

let ( * ) = compose
