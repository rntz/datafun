include Map.Make(String)
let of_list assocs = List.fold_left (fun map (k,v) -> add k v map) empty assocs
let remove_all keys map = List.fold_left (fun map k -> remove k map) map keys
