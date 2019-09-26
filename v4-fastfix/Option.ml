type 'a t = 'a option
let map f = function None -> None | Some x -> Some (f x)
let all (l: 'a option list): 'a list option =
  let rec loop acc = function
    | [] -> Some (List.rev acc)
    | None :: _xs -> None
    | Some x :: xs -> loop (x::acc) xs
  in loop [] l
