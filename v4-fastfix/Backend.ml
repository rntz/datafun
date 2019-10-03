open Passes
(* module Simplified = Simplify(ToHaskell) *)
module Renamed = PrettyName(ToHaskell)
module Simplified = Simplify(Renamed)
module Zeroed = ZeroChange(Simplified)
module Semi = Seminaive(Zeroed)
include Surface(Semi)

let fini x =
  x |> Zeroed.finish |> Simplified.finish
  |> Renamed.finish |> snd
  |> StringBuilder.finish

let finish (phi, delta) = fini phi, fini delta

let phiDeltaExpr (expr: term): tp * string * string =
  let tp, term = expr Cx.empty None in
  let phi, delta = finish term in tp, phi, delta
