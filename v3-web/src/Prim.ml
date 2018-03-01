type arith = [ `Add | `Sub | `Mul | `Div | `Mod ]
type cmp = [ `EQ | `LE | `GE | `GT | `LT ]
type prim = [ cmp | arith | `ElemOf | `Not ]

type infix = [ cmp | arith | `ElemOf ]
type prefix = [ `Not ]

let show_infix: infix -> string = function
  | `EQ -> "="
  | `LE -> "<=" | `GE -> ">="
  | `LT -> "<" | `GT -> ">"
  | `Add -> "+" | `Sub -> "-"
  | `Mul -> "*" | `Div -> "/" | `Mod -> "%"
  | `ElemOf -> "in?"

let show: prim -> string = function
  | `Not -> "not"
  | #infix as op -> "(" ^ show_infix op ^ ")"

let tone: [ cmp | arith ] -> Tone.tone * Tone.tone = function
  | `Add | `Mul -> `Id, `Id
  | `EQ | `Mod -> `Iso, `Iso
  | `LE | `LT -> `Op, `Id
  | `GE | `GT | `Sub | `Div -> `Id, `Op
