exception TODO of string
exception Impossible of string
exception TypeError of string

let todo msg = raise (TODO msg)
let impossible msg = raise (Impossible msg)
let typeError msg = raise (TypeError msg)

type sym = Sym.t
