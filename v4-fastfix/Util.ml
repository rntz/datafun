exception TODO of string
exception Impossible of string
exception TypeError of string

let todo msg = raise (TODO msg)
let impossible msg = raise (Impossible msg)
let typeError msg = raise (TypeError msg)

(* For the sake of record field name scope, it's nicer to declare this in Util
   (which I'll usually open) than in Sym (which I won't). *)
type sym = {name: string; id: int; degree: int}
