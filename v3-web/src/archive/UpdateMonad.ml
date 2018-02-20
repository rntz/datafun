open Sigs
open Util

(* A monoid equipped with a monoid action. *)
module type DELTA = sig
  type delta
  val zero: delta
  val ( * ): delta -> delta -> delta

  (* monoid action *)
  type state
  val apply: state -> delta -> state

  (* Laws:
   *
   * 1. (delta, zero, ( * )) is a monoid, that is:
   * - Associativity: a * (b * c) = (a * b) * c
   * - Identity:      a = a * zero = zero * a
   *
   * 2. apply is a right monoid action, that is:
   * - apply s zero s = s
   * - apply s (d1 * d2) = apply (apply s d1) d2
   *)
end

(* Update monads. These are nicely described in
 * http://cs.ioc.ee/~tarmo/tday-saka/uustalu-slides.pdf
 *
 * Don't be afraid of the "Cointerpreting directed containers" subtitle;
 * the core idea is not that complicated.
 *
 * We slightly optimize their version for the "imperative" case where
 * most updates are sequenced (ie. where >>= is much more common than
 * pass/censor/ignore), by returning an updated state as well as a delta.
 *
 * This does not address cases where Delta.* itself performs badly
 * (e.g. lists prefer being appended right-associatively).
 *)
module Update(D: DELTA) = struct
  include Monad(struct
    open D
    (* The returned `state` is the optimization mentioned above. *)
    type 'a t = state -> state * delta * 'a
    let pure x state = (state, zero, x)
    let (>>=) a f state =
      let (state1, delta1, x1) = a state in
      let (state2, delta2, x2) = f x1 state1 in
      (state2, D.(delta1 * delta2), todo())
  end)

  open D

  let get: state t = fun state -> (state, zero, state)
  let update: (state -> delta) -> unit t = fun f state ->
    let delta = f state in (apply state delta, delta, ())

  let pass: ((delta -> delta) * 'a) t -> 'a t = fun a state ->
    let (state1, delta, (filter, result)) = a state in
    let delta = filter delta in
    (apply state delta, delta, result)

  let listen: 'a t -> (delta * 'a) t = fun a state ->
    let (state1, delta, result) = a state in
    (state1, delta, (delta, result))

  let tell delta = update (const delta)
  let censor f a = pass (pure f ** a)
  let ignore a = censor (const zero)
end
