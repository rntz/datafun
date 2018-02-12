open Sigs
open Util

(* loc ::= (start_pos, end_pos) *)
type loc = Lexing.position * Lexing.position
type var = string
type tag = string
type prim = string
module Var = struct let show x = x end
module Tag = struct let show n = n end
module Prim = struct let show p = p end

type tone = [`Mono | `Anti | `Isos | `Path]
type base = [`Bool | `Int | `Str]

type tp =
  [ base
  | `Name of var
  | `Set of tp
  | `Box of tp
  | `Arrow of tp * tp
  | `Product of tp list
  | `Sum of (tag * tp) list ]

let base: base -> tp = fun x -> (x: base :> tp)

type eqtp =
  [ base
  | `Set of eqtp
  | `Box of eqtp
  | `Product of eqtp list
  | `Sum of (tag * eqtp) list ]

type semitp =
  [ `Bool
  | `Set of tp
  | `Arrow of tp * semitp
  | `Product of semitp list ]

let rec asSemilat: tp -> semitp option = function
  | `Bool -> Some `Bool
  | `Set a -> Some (`Set a)
  | `Arrow(a,b) -> asSemilat b |> Option.map (fun x -> `Arrow(a,x))
  | `Product ts -> Option.forEach ts asSemilat
                   |> Option.map (fun x -> `Product x)
  | _ -> None
