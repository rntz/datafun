open Util
open IL

exception Stuck of string
(* Internal error *)
exception NoMatch

module type VALUE = sig
  type set
  type t =
    | Bool of bool | Int of int | Str of string
    | Set of set
    | Tuple of t array
    | Tag of Ast.tag * t
    | Fn of (t -> t)
  val compare: t -> t -> int
  val eq: t -> t -> bool
  val show: t -> string
  val show_app: t -> string
  val show_atom: t -> string
end

module rec Values: Set.S with type elt = Value.t = Set.Make(Value)
and Value : VALUE with type set = Values.t = struct
  type set = Values.t
  type t
    = Bool of bool | Int of int | Str of string
    | Set of set
    | Tuple of t array
    | Tag of Ast.tag * t
    | Fn of (t -> t)

  (* We'll never actually end up comparing Fns because Datafun's
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

  let rec show: t -> string = function
    | Tuple xs -> String.concat "," (Array.(map show_app xs |> to_list))
    | e -> show_app e
  and show_app = function
    | Tag (n,x) -> Printf.sprintf "%s %s" n (show_atom x)
    | e -> show_atom e
  and show_atom = function
    | Bool true -> "true"
    | Bool false -> "false"
    | Int i -> Printf.sprintf "%d" i
    | Str s -> Printf.sprintf "%S" s
    | Set xs ->
       let f e strs = show_app e :: strs in
       "{" ^ (Values.fold f xs [] |> String.concat ", ") ^ "}"
    | Fn _ -> "<fn>"
    | e -> "(" ^ show e ^ ")"
end

type value = Value.t
open Value

(* Environments *)
type env = value Dict.t
let emptyEnv = Dict.empty
let lookup var env = Dict.find var env
let extend var value env = Dict.add var value env

let rec zero: semilat -> value = function
  | `Bool -> Bool false
  | `Tuple ts -> Tuple Array.(of_list ts |> map zero)
  | `Fn s -> Fn (fun _ -> zero s)
  | `Set -> Set Values.empty

let rec join (x: value) (y: value): value = match x,y with
  | Bool x, Bool y -> Bool (x || y)
  | Tuple xs, Tuple ys -> Tuple (Array.map2 join xs ys)
  | Set x, Set y -> Set (Values.union x y)
  | Fn f, Fn g -> Fn (fun x -> join (f x) (g x))
  | _ -> raise (Stuck "runtime type mismatch")

let rec eval (env: env): exp -> value = function
  | `Bool b -> Bool b | `Int i -> Int i | `Str s -> Str s
  | `Var v -> lookup v env
  | `Let(p,e,body) ->
     eval (destruct env p (eval env e)) body
  | `Lub(how,es) -> List.(map (eval env) es |> fold_left join (zero how))
  | `Eq(_,e1,e2) -> Bool (Value.eq (eval env e1) (eval env e2))
  | `Fix(fix, pat, step) ->
     let rec iter x =
       let next = eval (destruct env pat x) step in
       if Value.eq x next then x else iter next
     in iter (zero (fix :> semilat))
  (* introductions *)
  | `Lam(pat,body) -> Fn (fun arg -> eval (destruct env pat arg) body)
  | `Tuple ts -> Tuple Array.(of_list ts |> map (eval env))
  | `Tag(n,e) -> Tag(n, eval env e)
  | `Set es -> Set (Values.of_list (List.map (eval env) es))
  (* eliminations *)
  | `App(e1,e2) -> (match eval env e1 with
                    | Fn f -> f (eval env e2)
                    | _ -> raise (Stuck "applying non-function"))
  | `For(semilat, comps, body) ->
     let accum = ref (zero semilat) in
     let rec loop env = function
       | [] -> accum := join !accum (eval env body)
       | `When exp :: cs -> (match eval env exp with
                             | Bool b -> if b then loop env cs else ()
                             | _ -> raise (Stuck "runtime type error"))
       | `In (pat, exp) :: cs ->
          let visit elem = match matches env pat elem with
            | Some env -> loop env cs
            | None -> () in
          Values.iter visit (match eval env exp with
                             | Set es -> es
                             | _ -> raise (Stuck "runtime type error"))
     in loop env comps; !accum
  | `Case(subj, arms) ->
     let scrut = eval env subj in
     let rec examine = function
       | [] -> raise (Stuck "no pattern matched")
       | (pat, ifMatch) :: arms ->
          (match matches env pat scrut with
           | Some new_env -> eval new_env ifMatch
           | None -> examine arms)
     in examine arms

and destruct (env: env) (pat: pat) (subj: value): env =
  try doMatch env pat subj
  with NoMatch -> raise (Stuck "pattern failed to match")

and matches (env: env) (pat: pat) (subj: value): env option =
  try Some (doMatch env pat subj)
  with NoMatch -> None

and doMatch (env:env) (pat:pat) (subj: value) = match pat, subj with
  | `Wild, _ -> env
  | `Var v, _ -> extend v subj env
  | `Tuple ps, Tuple xs ->
     (try List.fold_left2 doMatch env ps (Array.to_list xs)
      with Invalid_argument _ -> raise NoMatch)
  | `Tag(n,p), Tag(m,x) -> if n == m then doMatch env p x else raise NoMatch
  | `Eq(_,exp), _ -> if Value.eq subj (eval env exp) then env else raise NoMatch
  | (`Tuple _ | `Tag _), _ -> raise (Stuck "type error in pattern match")
