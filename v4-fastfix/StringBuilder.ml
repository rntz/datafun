type t = string list -> string list
(* this assumes String.concat is efficient; if not, rewrite using Buffer. *)
let finish t = String.concat "" (t [])
let string s rest = s :: rest
let int i = string (string_of_int i)
let (^) x y rest = x (y rest)
let concat sep: t list -> t = function
  | [] -> fun s -> s
  | [t] -> t
  | t::ts -> fun rest ->
             t (List.fold_right (fun t rest -> sep (t rest)) ts rest)
