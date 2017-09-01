open Util

type loc = {start : Lexing.position; finish : Lexing.position}
type conid = string
type var = string

module V = Set.Make(String)

type tp = 
  | Int
  | Bool
  | String 
  | Set of tp 
  | Box of tp 
  | Arrow of tp * tp 
  | Product of tp list 
  | Sum of (conid * tp) list 


let rec print_closed = function
  | Int -> "int"
  | String -> "string"
  | Bool -> "bool"
  | Sum ctps -> String.concat "" ["[";
                                  String.concat " | " (List.map (fun (c, tp) -> 
                                                                   Printf.sprintf "%s : %s" c (print_type tp))
                                                                ctps);
                                  "]"]
  | tp -> String.concat "" ["("; print_type tp; ")"]
and print_unary tp = 
  match tp with 
  | Box tp -> String.concat " " ["box"; print_closed tp]
  | Set tp -> String.concat " " ["box"; print_closed tp]
  | tp     -> print_closed tp 
and print_product = function
  | Product [] -> "unit"
  | Product tps -> String.concat " * " (List.map print_unary tps)
  | tp -> print_unary tp 
and print_type = function 
  | Arrow(tp1, tp2) -> String.concat " -> " [print_product tp1; print_type tp2]
  | tp -> print_product tp 

                               
                 

                        
type pat = 
  | PVar 
  | PBool of bool
  | PString of string 
  | PBox of pat 
  | PTuple of pat list 
  | PCon of conid * pat 

type op = Plus | Minus | Times | Eq | Leq | Lt | Geq | Gt 
                      
type 'a expF = 
  | Var of var 
  | Abs of var * 'a 
  | Num of int 
  | Op of op * 'a * 'a 
  | Bool of bool
  | If of 'a * 'a * 'a 
  | Lam of pat * 'a 
  | App of 'a * 'a 
  | Tuple of 'a list 
  | Con of conid * 'a 
  | Case of 'a * (pat * 'a) list 
  | Singleton of 'a 
  | Join of 'a * 'a 
  | Bind of pat * 'a * 'a 
  | Box of 'a 
  | Annot of 'a * tp

let map f = function 
  | Var x -> Var x
  | Abs(x, a) -> Abs(x, f a)
  | Num n -> Num n 
  | Op(op, a, a') -> Op(op, f a, f a')
  | Bool b -> Bool b
  | If(a, a', a'') -> If(f a, f a', f a'')
  | Lam(p, a) -> Lam(p, f a)
  | App(a, a') -> App(f a, f a')
  | Tuple as' -> Tuple (List.map f as')
  | Con(c, a) -> Con(c, f a)
  | Case(a, pas) -> Case(f a, List.map (fun (p, a) -> (p, f a)) pas)
  | Singleton a -> Singleton (f a)
  | Join(a, a') -> Join(f a, f a')
  | Bind(p, a, a') -> Bind(p, f a, f a')
  | Annot(a, tp) -> Annot(f a, tp)
  | Box a -> Box (f a)

module Seq(M : IDIOM) = struct
  open M 
  module L = Util.Seq(M)
                     
  let seq (e : 'a M.t expF) : 'a expF M.t = 
    match e with
     | Var x -> return (Var x)
     | Abs (x,m) -> m |> map (fun a -> Abs(x, a))
     | Num n -> return (Num n)
     | Op (op, e', e'') -> (e' ** e'') |> map (fun (a', a'') -> Op(op, a', a''))
     | Bool b -> return (Bool b)
     | If (e1, e2, e3) -> (e1 ** e2 ** e3) |> map (fun (a1, (a2, a3)) -> If(a1, a2, a3))
     | Lam (p, e') -> e' |> map (fun a -> Lam(p, a))
     | App (e1, e2) -> e1 ** e2 |> map (fun (a1, a2) -> App(a1, a2))
     | Tuple es' -> L.list es' |> map (fun as' -> Tuple as')
     | Con (c, e') -> e' |> map (fun a -> Con(c, a))
     | Case (e, pes) -> let (ps, es) = List.split pes in 
                        e ** L.list es |> map (fun (a, as') -> Case(a, List.combine ps as'))
     | Singleton e' -> e' |> map (fun a -> Singleton a)
     | Join(e', e'') -> (e' ** e'') |> map (fun (a',a'') -> Join(a', a''))
     | Bind(p, e', e'') -> (e' ** e'') |> map (fun (a',a'') -> Bind(p, a', a''))
     | Annot(e, tp) -> e |> map (fun a -> Annot(a, tp))
     | Box e -> e |> map (fun a -> Box a)
end

type exp = In of loc * V.t * exp expF 

let out (In(_, _, e)) = e 
let fvs (In(_, vs, _)) = vs 
let loc (In(loc, _, _)) = loc 

let rename_id x y z = if x = z then y else z 

module VarMonoid = struct
    type 'a t = V.t
    let map f x = x 
    let unit () = V.empty
    let ( ** ) = V.union
  end

let into loc e = 
  match e with
  | Var x -> In(loc, V.singleton x, Var x)
  | Abs(x, e) -> In(loc, V.remove x (fvs e), Abs(x, e))
  | e -> let module M = Seq(MkIdiom(VarMonoid))  in
         In(loc, M.seq (map fvs e), e)


let rec rename x y e = 
  into (loc e) (match out e with 
                | Var z -> Var (rename_id x y z)
                | Abs(z, e) -> Abs(rename_id x y z, rename x y e)
                | ebody -> map (rename x y) ebody)
           
  


