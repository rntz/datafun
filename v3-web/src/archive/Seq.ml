open Util

(* "Lazy" tree representations of sequences. *)
type 'a seq = 'a tree ref
and 'a tree =
  | Leaf of 'a array
  | Cons of 'a * 'a tree
  | Snoc of 'a tree * 'a
  | Append of 'a tree * 'a tree
  (* Previously: Concat of 'a tree array *)
  | Concat of 'a seq tree

let rec tree_array_fold: 'a 'b. ('b -> 'a -> 'a) -> ('b array -> 'a -> 'a)
                         -> 'b tree -> 'a -> 'a
  = fun onElem onArray ->
  let rec visit t init = match t with
    | Leaf xs -> onArray xs init
    | Cons (x,xs) -> onElem x (visit xs init)
    | Snoc (xs,x) -> visit xs (onElem x init)
    | Append (t,u) -> visit t (visit u init)
    | Concat ts -> tree_fold (fun t -> visit !t) ts init
  in visit

and tree_fold: 'a 'b. ('b -> 'a -> 'a) -> 'b tree -> 'a -> 'a =
  fun f -> tree_array_fold f (Array.fold_right f)

let tree_mapreduce f combine zero tree =
  tree_fold (fun acc x -> combine (f acc) x) tree zero

let tree_size (t: 'a tree): (int * 'a) option =
  let combine x y = match x,y with
    | Some (n,x), Some (m,y) -> Some (n+m,x)
    | x, None -> x
    | None, x -> x
  in tree_mapreduce (fun x -> Some (1,x)) combine None t

let eval (tree: 'a tree): 'a array =
  match tree_size tree with
  | None -> [||]
  | Some (size, elem) ->
     let array = Array.make size elem in
     let visitElem elem offset = Array.set array offset elem; offset+1 in
     let visitArray elems offset =
       let n = Array.length elems in
       Array.blit elems 0 array offset n; offset + n
     in
     ignore (tree_array_fold visitElem visitArray tree 0);
     array


(* Sequences; trees lazily evaluated to arrays. *)
(* Recall that:
 * type 'a seq = 'a tree ref *)

let to_array_unsafe t = match !t with
  | Leaf array -> array
  | e -> let array = eval e in t := Leaf array; array
let to_array t = match !t with
  | Leaf array -> Array.copy array
  | _ -> to_array_unsafe t
let to_list t = Array.to_list (to_array_unsafe t)

let of_array_unsafe a = ref (Leaf a)
let of_array a = of_array_unsafe (Array.copy a)
let of_list l = of_array_unsafe (Array.of_list l)

let force t = ignore (to_array_unsafe t); t

let size x = Array.length (to_array_unsafe x)
let null x = 0 = size x

let mkEmpty () = ref (Leaf [||])
let singleton x = ref (Leaf [| x |])
let cons x xs = ref (Cons (x, !xs))
let snoc xs x = ref (Snoc (!xs,x))
let append xs ys = ref (Append (!xs,!ys))
let concat ts = ref (Concat !ts)
let concat_array ts = concat (of_array ts)
let concat_list ts = concat_array (Array.of_list ts)

let map f t = of_array_unsafe (Array.map f (to_array_unsafe t))
let fold_right f t = Array.fold_right f (to_array_unsafe t)
let fold_left f init t = Array.fold_left f init (to_array_unsafe t)
