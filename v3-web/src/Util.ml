open Sigs

exception Bug of string
exception TODO
let todo() = raise TODO
let bug msg = raise (Bug msg)

let id x = x
(* let const x _y = x *)
(* let curry f x y = f (x,y) *)
(* let uncurry f (x,y) = f x y *)
(* let flip f x y = f y x *)
let pair x y = (x,y)
(* let apply (f,x) = f x *)
let cons (x,xs) = x :: xs
(* let compose f g x = f (g x)
 * let (<@) f g = compose f g
 * let (@>) g f = compose f g *)
(* Like $ in haskell. Needs wonky name for right-associativity.
 * Apparently this is "@@" in the standard library since 4.01?
 * TODO: check that it's in bucklescript & use "@@" instead. *)
let ( **> ) f x = f x

module Idiom(A: IDIOMATIC): IDIOM with type 'a t = 'a A.t = struct
  include A
  let ($) = map
  let (=>) x f = f $ x
  (* let (>>) x y = snd $ (x ** y) *)
  (* let (<*\) x y = fst $ (x ** y) *)

  (* let app fc ac = apply $ (fc ** ac) *)
  (* let pair (x,y) = x ** y *)
  (* let option = function | None -> pure None | Some c -> c => (fun x -> Some x) *)
  (* let result = function | Error v -> pure (Error v) | Ok c -> map (fun x -> Ok x) c *)
  let rec list = function | [] -> pure [] | m::ms -> cons $ m ** list ms
  (* let forEach lst f = list (List.map f lst) *)

  (* let onPair f g (x,y) = f x ** g y
   * let onFst f = onPair f pure
   * let onSnd g = onPair pure g *)
end

module Monad(M: MONADIC): MONAD with type 'a t = 'a M.t = struct
  include M
  let map f k = k >>= fun x -> pure (f x)
  let concat c = c >>= id
  let ( ** ) c d = c >>= fun x -> map (pair x) d
  include (Idiom(struct include M let map = map let ( ** ) = ( ** ) end)
           : IDIOM with type 'a t := 'a M.t)
end


(* Lists & Options are Monads. *)
module Lists = Monad(struct include List
                            type 'a t = 'a list
                            let pure x = [x]
                            let (>>=) x f = concat (map f x)
                     end)

module Option = struct
  include Monad(struct
    type 'a t = 'a option
    let pure x = Some x
    let (>>=) x f = match x with Some x -> f x | None -> None
  end)

  let elim ifNone ifSome = function | None -> ifNone | Some x -> ifSome x
  let default ifNone = elim ifNone id
end
