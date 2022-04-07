exception TODO of string
exception Impossible of string
exception TypeError of string
exception ParseError of string

let todo msg = raise (TODO msg)
let impossible msg = raise (Impossible msg)
let typeError msg = raise (TypeError msg)
let parseError msg = raise (ParseError msg)

type sym = Sym.t
