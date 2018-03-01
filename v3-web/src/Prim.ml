type compare = [ `EQ | `LE | `GE | `GT | `LT ]
type arith = [ `Plus | `Minus | `Times | `Div | `Modulo ]

type prim = [ `Cmp of compare
            | `Arith of arith
            | `ElemOf
            | `Not ]

type infix = [ `Cmp of compare | `Arith of arith | `ElemOf ]
type prefix = [ `Not ]

let show_infix: infix -> string = function
  | `Cmp `EQ -> "="
  | `Cmp `LE -> "<=" | `Cmp `GE -> ">="
  | `Cmp `LT -> "<" | `Cmp `GT -> ">"
  | `Arith `Plus -> "+" | `Arith `Minus -> "-"
  | `Arith `Times -> "*" | `Arith `Div -> "/" | `Arith `Modulo -> "%"
  | `ElemOf -> "in?"

let show: prim -> string = function
  | `Not -> "not"
  | #infix as op -> "(" ^ show_infix op ^ ")"
