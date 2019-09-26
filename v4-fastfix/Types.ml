open Util

type 'a cx = 'a Cx.t

type ('a,'b) weird = [ `Bool | `String | `Set of 'a | `Tuple of 'b list ]
type eqtp = (eqtp, eqtp) weird
type firstorder = [ `Bool | `String | `Set of eqtp ]
type 'a maketypes = [ (eqtp, 'a) weird | `Fn of 'a * 'a ]

(* Frontend, modal types. *)
type modaltp = [ modaltp maketypes | `Box of modaltp ]
(* Backend, non-modal types. *)
type rawtp = rawtp maketypes
(* Semilattices, parameterized by underlying types *)
type 'a semilat =
  [ `Bool
  | `Set of eqtp
  | `Tuple of 'a semilat list
  | `Fn of 'a * 'a semilat ]

type mode = Id | Box | Hidden
type modalcx = (mode * modaltp) Cx.t

let rec firstOrder: modaltp -> eqtp option = function
  | #firstorder as a -> Some a
  | `Fn _ | `Box _ -> None
  | `Tuple tps ->
     Option.(List.map firstOrder tps |> all |> map (fun x -> `Tuple x))

let rec debox: modaltp -> rawtp = function
  | #firstorder as a -> a
  | `Box a -> debox a
  | `Fn (a,b) -> `Fn (debox a , debox b)
  | `Tuple tps -> `Tuple List.(map debox tps)

(* phi corresponds to Φ, except it drops □. *)
let rec phi: modaltp -> rawtp = function
  | #firstorder as a -> a
  | `Tuple tps -> `Tuple (List.map phi tps)
  | `Box a -> (`Tuple [phi a; delta a])
  | `Fn (a,b) -> `Fn (phi a, phi b)

(* delta corresponds to ΔΦ (_not_ to Δ alone), except it drops □. *)
and delta: modaltp -> rawtp = function
  | (`Bool | `Set _) as a -> a
  | `String | `Box _ -> `Tuple []        (* discrete types don't change *)
  | `Tuple tps -> `Tuple List.(map delta tps)
  | `Fn (a,b) -> `Fn(phi a, `Fn(delta a, delta b))

let phiDelta x = phi x, delta x

(* Convince OCaml's type system of various refinement properties. *)
let firstOrderLat: modaltp semilat -> eqtp semilat option = Obj.magic firstOrder
let deboxLat: modaltp semilat -> rawtp semilat = Obj.magic debox
let deltaEq: eqtp -> eqtp = Obj.magic delta
let phiLat: modaltp semilat -> rawtp semilat = Obj.magic phi
let deltaLat: modaltp semilat -> rawtp semilat = Obj.magic delta
let phiDeltaLat: modaltp semilat -> rawtp semilat * rawtp semilat =
  Obj.magic phiDelta

let rec asLat: 'a -> 'a semilat = function
  | `Bool -> `Bool
  | `Set a -> `Set a
  | `Fn (a,b) -> `Fn (a, asLat b)
  | `Tuple tps -> `Tuple (List.map asLat tps)
  | `String | `Box _ -> typeError "not a semilattice type"

let isLat (x: 'a): 'a semilat option =
  try Some (asLat x) with TypeError _ -> None
