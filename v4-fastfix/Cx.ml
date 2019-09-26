include Map.Make(Sym)
(* Prefers later bindings to earlier ones. *)
let from_list l = List.fold_left (fun cx (k,v) -> add k v cx) empty l
let add_list l cx = union (fun _k x _y -> Some x) (from_list l) cx
let add_opt k vopt cx = match vopt with None -> cx | Some v -> add k v cx
