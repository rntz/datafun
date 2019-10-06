open Passes
(* module Renamed = PrettyName(ToHaskell) *)
module Renamed = PrettyName(Pretty)
module Simplified = Simplify(Renamed)
(* module Simplified = Simplify(ToHaskell) *)
module Zeroed = ZeroChange(Simplified)
module Semi = Seminaive(Zeroed)
include Surface(Semi)
