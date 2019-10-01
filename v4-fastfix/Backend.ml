open Passes
module Simplified = Simplify(ToHaskell)
module Zeroed = ZeroChange(Simplified)
module Semi = Seminaive(Zeroed)
include Surface(Semi)

let finish (phi, delta) = 
  StringBuilder.finish (Simplified.finish (Zeroed.finish phi)),
  StringBuilder.finish (Simplified.finish (Zeroed.finish delta))

let phiDeltaExpr (expr: term): tp * string * string =
  let tp, term = expr Cx.empty None in
  let phi, delta = finish term in tp, phi, delta
