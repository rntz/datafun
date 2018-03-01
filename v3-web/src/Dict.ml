include Map.Make(String)
let of_list (assocs: (string * 'a) list): 'a t =
  List.fold_left (fun map (k,v) -> add k v map) empty assocs
