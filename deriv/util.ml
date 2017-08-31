module type FUNCTOR = sig
  type 'a t 
  val map : ('a -> 'b) -> 'a t -> 'b t 
end

module type MONAD = sig
  include FUNCTOR 
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t 
end

module type MONOIDAL = sig
  include FUNCTOR 
  val unit : unit -> unit t 
  val ( ** ) : 'a t -> 'b t -> ('a * 'b) t 
end
                      
module type IDIOM = sig
  include MONOIDAL 

  val return : 'a -> 'a t
  val app : ('a -> 'b) t -> 'a t -> 'b t 
end
                      

module type SEQ = sig
  type 'a t 

  val pair : 'a t * 'b t -> ('a * 'b) t 
  val option : 'a t option -> 'a option t 
  val result : ('a t, 'b) result -> ('a,'b) result t 
  val list : 'a t list -> 'a list t
end 

module MkIdiom(M : MONOIDAL) : (IDIOM with type 'a t = 'a M.t) = struct
  include M

  let return x = map (fun () -> x) (unit())
  let app f x = map (fun (f, x) -> f x) (f ** x)
end
                                                 
                                                   

module Monoidal(M : MONAD) : (IDIOM with type 'a t = 'a M.t) = struct
  include MkIdiom(struct 
    type 'a t = 'a M.t

    let map = M.map 
                
    let unit () = M.return () 

    let ( ** ) m1 m2 = let open M in 
                       m1 >>= fun v1 -> 
                       m2 >>= fun v2 -> 
                       return (v1, v2)
                 end)
end

module Seq(A : IDIOM) : SEQ with type 'a t = 'a A.t = struct
  type 'a t = 'a A.t

  open A

  let option = function
    | None -> return None
    | Some c -> app (return (fun v -> Some v)) c 

  let result = function 
    | Error v -> return (Error v)
    | Ok c -> app (return (fun v -> Ok v)) c

  let pair (c, c') = c ** c'
                  
  let cons (x, xs) = x :: xs 

  let rec list = function
    | [] -> return []
    | m :: ms -> map cons (m ** (list ms))
end

module Pair = struct
  type ('a, 'b) t = 'a * 'b 
  let fst = fst
  let snd = snd 
  let map f g (x, y) = (f x, g y)
  let pair f g x = (f x, g x)

  let swap (a, b) = (b, a)
  let assoc (a, (b, c)) = ((a, b), c)
  let assoc' ((a, b), c) = (a, (b, c))

  let unit (a, ()) = a
  let unit' ((), a) = a 
                     
end


module Result = struct
  type ('a, 'b) t = ('a, 'b) result

  let ok v = Ok v 
  let error v = Error v 

  let result f g = function
    | Ok x -> f x 
    | Error y -> g y 

  let map f g = function
    | Ok v -> Ok (f v)
    | Error e -> Error (g e)

  let return = ok 
  let (>>=) m f = 
    match m with
    | Ok v -> f v 
    | Error e -> Error e 
end

module Option = struct
  type 'a t = 'a option 

  let some v = Some v 
  let none = None

  let option f y = function
    | Some x -> f x
    | None -> y 

  let map f = function
    | Some v -> Some (f v)
    | None -> None

  let return = some 
  let (>>=) m f = 
    match m with
    | Some v -> f v 
    | None -> None

  include (Monoidal(struct
                     type 'a t = 'a option
                     let map = map 
                     let return = return
                     let (>>=) = (>>=)
                   end): IDIOM with type 'a t := 'a option)
end

module Fn = struct
  let curry f a b = f (a, b)
  let uncurry f (a, b) = f a b 
  let flip f x y = f y x 
  let id x = x 
  let compose f g x = f (g x)
  let (@) f g x = g (f x)
  let map f g h x = g (h (f x))
end

                  

                  
