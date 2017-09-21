open Ast

type tone = Disc | Mono

type hyp = Var of tp * tone | HideMono

type ctx = (var * hyp) list

type state = { sym : int; ctx : ctx; loc : loc}

type error = string * loc

type 'a t = state -> ('a * state, error) result

let return : 'a -> 'a t = fun x s -> Ok(x, s)

let (>>=) : 'a t -> ('a -> 'b t) -> 'b t =
  fun m f s ->
  match m s with
  | Ok(v, s) -> f v s
  | Error msg -> Error msg

let map f m = m >>= fun v -> return (f v)

let gensym x s = let sym = Printf.sprintf "%s_%d" x s.sym in
                 Ok(sym, {s with sym = 1 + s.sym})

let fail : ('a, unit, string, 'b t) format4 -> 'a =
  fun fmt -> Printf.ksprintf (fun msg s-> Error (msg, s.loc)) fmt

let setloc loc : unit t = fun s -> Ok((), {s with loc = loc})
let getloc : loc t = fun s -> Ok(s.loc, s)

let out e =
  match Ast.out e with
  | Abs(x, e) -> gensym x >>= fun y ->
                 setloc (loc e) >>= fun () ->
                 return (Abs(y, rename x y e))
  | ebody     -> return ebody

let into e =
  getloc >>= fun loc ->
  return (Ast.into loc e)

let getctx : ctx t = fun s -> Ok(s.ctx, s)

let lookup : var -> (tp * tone) t = fun x ->
  let rec loop hidemono = function
    | [] -> fail "Unbound variable '%s'" x
    | (y, HideMono) :: ctx when x = y -> assert false
    | (y, HideMono) :: ctx -> loop true ctx
    | (y, Var(tp, Mono)) :: ctx when x = y && hidemono -> fail "Unavailable monotone variable '%s'" x
    | (y, Var(tp, tone)) :: ctx when x = y -> return (tp, tone)
    | (y, Var(tp, tone)) :: ctx -> loop hidemono ctx
  in
  getctx >>= fun ctx ->
  loop false ctx

let with_hyp : var * tp * tone -> 'a t -> 'a t =
  fun (x, tp, tone) m  s ->
  let s' = {s with ctx = (x, Var(tp, tone)) :: s.ctx} in
  match m s' with
  | Error e -> Error e
  | Ok(v, s'') -> Ok(v, {s'' with ctx = List.tl s''.ctx})

let hidemono : 'a t -> 'a t =
  fun m ->
  gensym "hide" >>= fun x s ->
  let s' = {s with ctx = (x, HideMono) :: s.ctx} in
  match m s' with
  | Error e -> Error e
  | Ok(v, s'') -> Ok(v, {s'' with ctx = List.tl s''.ctx})




module Seq : Util.SEQ with type 'a t := 'a t =
  Util.Seq(Util.Monoidal(struct
                          type nonrec 'a t = 'a t
                          let return = return
                          let (>>=) = (>>=)
                          let map = map
                        end))
