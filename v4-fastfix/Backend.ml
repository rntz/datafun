open Passes
module Simplified = Simplify(ToHaskell)
module Zeroed = ZeroChange(Simplified)
module Semi = Seminaive(Zeroed)
include Typecheck(Semi)

let finish (phi, delta) = 
  StringBuilder.finish (Simplified.finish (Zeroed.finish phi)),
  StringBuilder.finish (Simplified.finish (Zeroed.finish delta))

let phiDeltaTerm (tp: tp) (term: term): string * string = finish (term Cx.empty tp)
let phiDeltaExpr (expr: expr): tp * string * string =
  let tp, term = expr Cx.empty in
  let phi, delta = finish term in tp, phi, delta

let phiTerm tp term = fst (phiDeltaTerm tp term)
let phiExpr expr = let tp,phi,_delta = phiDeltaExpr expr in tp,phi
