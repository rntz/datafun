open Sigs

exception TODO
let todo() = raise TODO

let id x = x
let curry f x y = f (x,y)
let uncurry f (x,y) = f x y
let flip f x y = f y x
let pair x y = (x,y)
let apply (f,x) = f x
let cons (x,xs) = x :: xs
let compose f g x = f (g x)
let (<@) f g = compose f g
let (@>) g f = compose f g
let (@@) f x = f x

module Idiom(A: IDIOMATIC): IDIOM with type 'a t = 'a A.t = struct
  include A
  let app fc ac = map apply (fc ** ac)
  let pair (x,y) = x ** y
  let option = function | None -> pure None | Some c -> map (fun x -> Some x) c
  (* let result = function | Error v -> pure (Error v) | Ok c -> map (fun x -> Ok x) c *)
  let rec list = function | [] -> pure [] | m::ms -> map cons (m ** list ms)
  let forEach lst f = list (List.map f lst)
  let (=>) x f = map f x
  let (>>) x y = map snd (x ** y)
  let (<*) x y = map fst (x ** y)
end

module Monad(M: MONADIC): MONAD with type 'a t = 'a M.t = struct
  include M
  let (>>=) c f = concat (map f c)
  let ( ** ) c d = c >>= fun x -> map (pair x) d
  include (Idiom(struct include M let ( ** ) = ( ** ) end)
           : IDIOM with type 'a t := 'a M.t)
end

(* The identity monad. More useful in OCaml than it is in Haskell. *)
module Identity = Monad(struct type 'a t = 'a let pure = id let map = id let concat = id end)


(* Traversables *)
module Traverse(T: TRAVERSABLE): TRAVERSE with type 'a t = 'a T.t =
struct
  type 'a t = 'a T.t
  module Seq(M: IDIOM) = struct
    include T.Seq(M)
    let seq x = traverse id x
  end
  module TId = T.Seq(Identity)
  let map = TId.traverse
end

(* Lists & Options are both Monad and Traversable. *)
module Lists = struct
  include Monad(struct include List type 'a t = 'a list let pure x = [x] end)
  include (Traverse(struct
    type 'a t = 'a list
    module Seq(M: IDIOM) = struct
      let rec traverse f = function
        | [] -> M.pure []
        | x::xs -> M.(map cons (f x ** traverse f xs))
    end
  end) : TRAVERSE with type 'a t := 'a list)
end

module Option = struct
  include Monad(struct
    type 'a t = 'a option
    let pure x = Some x
    let map f = function Some x -> Some (f x) | None -> None
    let concat = function Some (Some x) -> Some x | _ -> None
  end)
  include (Traverse(struct
    type 'a t = 'a option
    module Seq(M: IDIOM) = struct
      let traverse f = function
        | Some x -> M.map (fun x -> Some x) (f x)
        | None -> M.pure None
    end
  end) : TRAVERSE with type 'a t := 'a option)

  let elim ifNone ifSome = function | None -> ifNone | Some x -> ifSome x
  let default ifNone = elim ifNone id
end
