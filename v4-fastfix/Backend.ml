open Passes
(* module Renamed = PrettyName(ToHaskell) *)
module Renamed = PrettyName(Pretty)
module Simplified = Simplify(Renamed)
(* module Simplified = Simplify(ToHaskell) *)
module Zeroed = ZeroChange(Simplified)
module Semi = Seminaive(Zeroed)
include Surface(Semi)

let fini x =
  x |> Zeroed.finish |> Simplified.finish
  |> Renamed.finish |> snd
  |> (fun tm -> let buf = Buffer.create 80 in
                let out = Format.formatter_of_buffer buf in
                Pretty.finish tm out;
                Format.pp_print_flush out ();
                Buffer.contents buf)
  (* |> StringBuilder.finish *)

let finish (phi, delta) = fini phi, fini delta

let phiDeltaExpr (expr: term): tp * string * string =
  let tp, term = expr Cx.empty None in
  let phi, delta = finish term in tp, phi, delta
