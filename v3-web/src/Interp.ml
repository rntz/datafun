open Util
open Backend

exception Stuck of string

module type VALUE = sig
  type set
  type t =
    | Bool of bool | Int of int | Str of string
    | Set of set
    | Tuple of t array
    | Tag of Ast.tag * t
    | Func of (t -> t)
  val compare: t -> t -> int
  val eq: t -> t -> bool
end

module rec Values: Set.S with type elt = Value.t = Set.Make(Value)
and Value : VALUE with type set = Values.t = struct
  type set = Values.t
  type t
    = Bool of bool | Int of int | Str of string
    | Set of set
    | Tuple of t array
    | Tag of Ast.tag * t
    | Func of (t -> t)

  (* We'll never actually end up comparing Funcs because Datafun's
   * type system prohibits sets of non-first-order types.
   *
   * But we WILL end up comparing Sets, which means we can't use
   * Pervasives.compare! Argh!
   *
   * If I used Jane Street's Base and %ppx_compare, this would all
   * sort itself out. *)
  let rec compare x y = match x,y with
    | (Bool _, Bool _) | (Int _, Int _) | (Str _, Str _)
      -> Pervasives.compare x y
    | Set xs,    Set ys     -> Values.compare xs ys
    | Tuple xs,  Tuple ys   ->
       let n = Array.length xs in
       let rec f i = if i = n then 0 else
                     let c = compare (Array.get xs i) (Array.get ys i) in
                     if c <> 0 then c else f (i+1)
       in f 0
    | Tag (n,x), Tag (m,y)  ->
       let cmp1 = String.compare n m in
       if cmp1 <> 0 then cmp1 else compare x y
    | _, _ -> raise (Stuck "cannot compare those values")

  let eq x y = 0 = compare x y
end

type value = Value.t
open Value

(* A stack of variables. *)
type env = value list

let rec zero: semilat -> value = function
  | `Bool -> Bool false
  | `Tuple ts -> Tuple Array.(of_list ts |> map zero)
  | `Func s -> Func (fun _ -> zero s)
  | `Set -> Set Values.empty

let rec join (x: value) (y: value): value = match x,y with
  | Bool x, Bool y -> Bool (x || y)
  | Tuple xs, Tuple ys -> Tuple (Array.map2 join xs ys)
  | Set x, Set y -> Set (Values.union x y)
  | Func f, Func g -> Func (fun x -> join (f x) (g x))
  | _ -> raise (Stuck "runtime type mismatch")

let rec eval (env: env): exp -> value = function
  | `Bool b -> Bool b | `Int i -> Int i | `Str s -> Str s
  | `Stuck msg -> raise (Stuck msg)
  | `Var ix -> List.nth env ix
  | `Let(x,e,body) -> eval (eval env e :: env) body
  | `Lub(how,es) -> List.(map (eval env) es |> fold_left join (zero how))
  | `Eq(_,e1,e2) -> Bool (Value.eq (eval env e1) (eval env e2))
  | `Fix(init, x, step) ->
     let rec f x = let next = eval (x::env) step in
                   if Value.eq x next then x else f next
     in f (eval env init)
  (* introductions *)
  | `Lam(n,body) -> Func (fun arg -> eval (arg::env) body)
  | `Tuple ts -> Tuple Array.(of_list ts |> map (eval env))
  | `Tag(n,e) -> Tag(n, eval env e)
  | `MkSet es -> Set (Values.of_list (List.map (eval env) es))
  (* eliminations *)
  | `App(e1,e2) ->
     (match eval env e1 with
      | Func f -> f (eval env e2)
      | _ -> raise (Stuck "applying non-function"))
  | `IfThenElse(cnd,thn,els) ->
     eval env (match eval env cnd with
               | Bool b -> if b then thn else els
               | _ -> raise (Stuck "not a boolean"))
  | `For(how, setExp, (x, bodyExp)) ->
     let s = match eval env setExp with | Set vs -> vs
                                        | _ -> raise (Stuck "not a set")
     in Values.fold join s (zero how)
  | `Case(subj, arms) ->
     let scrut = eval env subj in
     let rec examine = function
       | [] -> raise (Stuck "no pattern matched")
       | (pat, ifMatch) :: arms ->
          (match matches env scrut pat with
           | Some new_env -> eval new_env ifMatch
           | None -> examine arms)
     in examine arms

and matches (env: env) (scrut: value): pat -> env option = function
  | `Wild -> Some env
  | `Var x -> Some (scrut :: env)
  | `Tuple ps -> (match scrut with
    | Tuple vs ->
       let rec recur env i = function
         | [] -> Some env
         | p::ps -> (match matches env (Array.get vs i) p with
                     | Some env' -> recur env' (i+1) ps
                     | None -> None)
       in recur env 0 ps
    | _ -> None)
  | `Tag(n,p) -> (match scrut with | Tag(m,v) when n = m -> matches env v p | _ -> None)
  | `Eq(_,exp) -> if Value.eq scrut (eval env exp) then Some env else None
