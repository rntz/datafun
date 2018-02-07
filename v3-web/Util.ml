open Sigs

exception TODO

let id x = x
let curry f x y = f (x,y)
let uncurry f (x,y) = f x y
let flip f x y = f y x
let pair x y = (x,y)
let apply (f,x) = f x
let cons (x,xs) = x :: xs

module Idiom(A: IDIOMATIC): IDIOM with type 'a t = 'a A.t = struct
  include A
  let app fc ac = map apply (fc ** ac)
  let pair (x,y) = x ** y
  let option = function | None -> pure None | Some c -> map (fun x -> Some x) c
  let result = function | Error v -> pure (Error v) | Ok c -> map (fun x -> Ok x) c
  let rec list = function | [] -> pure [] | m::ms -> map cons (m ** list ms)
  let forEach lst f = list (List.map f lst)
end

module Monad(M: MONADIC): MONAD with type 'a t = 'a M.t = struct
  include M
  let (>>=) c f = concat (map f c)
  let ( ** ) c d = c >>= fun x -> map (pair x) d
  include (Idiom(struct include M let ( ** ) = ( ** ) end)
           : IDIOM with type 'a t := 'a M.t)
end


(* Some monads & monad transformers *)
module Id = Monad(struct type 'a t = 'a let pure = id let map = id let concat = id end)
module Lists = Monad(struct include List type 'a t = 'a list let pure x = [x] end)

module WriterT(M: MONAD)(W: MONOID) = Monad(struct
  open W
  type 'a t = (W.t * 'a) M.t
  let pure x = M.pure (monoid.empty, x)
  let map f = M.map (fun (w,x) -> (w, f x))
  let concat (c: 'a t t): 'a t =
    M.(c >>= fun (u,d) -> d >>= fun (v,x) ->
       pure (monoid.append u v, x))
end)

module Writer = WriterT(Id)


(* Traversables *)
module Traverse(T: TRAVERSABLE): TRAVERSE with type 'a t = 'a T.t =
struct
  type 'a t = 'a T.t
  module Seq(M: IDIOM) = struct
    include T.Seq(M)
    let seq x = traverse id x
  end
  module TId = T.Seq(Id)
  let map = TId.traverse
end
