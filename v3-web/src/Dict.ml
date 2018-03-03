include Map.Make(String)
(* NB. bindings later in `assocs` win.
 * of_list [1,"early"; 1,"late"] == of_list [1,"late"] *)
let of_list assocs = List.fold_left (fun map (k,v) -> add k v map) empty assocs
let remove_all keys map = List.fold_left (fun map k -> remove k map) map keys
