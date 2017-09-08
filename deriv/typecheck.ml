open Ast
open Util 
open Context

let rec replicate x = function
  | 0 -> []
  | n -> x :: replicate x (n - 1)

let rec break n xs = 
  match n, xs with
  | 0, xs -> ([], xs)
  | n, [] -> assert false
  | n, x :: xs -> let (ys, zs) = break (n-1) xs in
                  (x :: ys, zs)

let rec mkAbs (us, e) = 
  match us with
  | [] -> e 
  | u :: us -> Ast.into (loc e) (Abs(u, mkAbs(us, e)))

let lam (u, e) = into (Lam(PVar, mkAbs([u], e)))

let let_ (x, e1, e2) = into (Let(e1, mkAbs([x], e2)))

let bind_ (x, e1, e2) = into (Bind(PVar, e1, mkAbs([x], e2)))

let let_tuple xs e1 e2 = into (LetTuple(List.length xs, e1, mkAbs(xs, e2)))


let rec find_var = function
  | (PVar :: ps, e) -> (match Ast.out e with
                        | Abs(x, e) -> Some x
                        | _ -> assert false)
  | (p :: ps, e) -> None
  | ([], e) -> assert false 

let find_var_list arms : Ast.var option = 
  let rec loop = function
    | [] -> None
    | (Some x) :: xs -> Option.return x 
    | None :: xs -> loop xs 
  in 
  loop (List.map find_var arms)
                        
let unabs y e = 
  match Ast.out e with
  | Abs(x, e) -> rename x y e
  | _ -> assert false 
                              



let expect sort tp = fail "Expected %s type, got '%s'" sort (print_type tp)
let mismatch tp tp' = fail "Expected '%s' inferred '%s'" (print_type tp) (print_type tp')

let op_type (op : op) = 
  match op with
  | Plus -> (Int, Int, Int)
  | Minus -> (Int, Int, Int)
  | Times -> (Int, Int, Int)
  | Eq -> (Int, Int, Bool)
  | Leq -> (Int, Int, Bool)
  | Lt -> (Int, Int, Bool)
  | Geq -> (Int, Int, Bool)
  | Gt -> (Int, Int, Bool)

let rec leading_var arms = 
  List.for_all (function
                | (PVar :: _, _) -> true
                | _ -> false)
               arms

let rebind u e = 
  match Ast.out e with
  | Abs(_, _) -> let into = Ast.into (Ast.loc e) in
                 into (Let(into (Var u), e))
  | _ -> assert false

let split_on_var u = 
  let split = function
    | (PVar :: ps, e) -> (ps, rebind u e)
    | (PWild :: ps, e) -> (ps, e)
    | (_, e) -> assert false
  in
  List.map split

let split_tuple u n arms = 
  let split = function
    | ((PTuple ps) :: ps', e) -> if List.length ps = n then 
                                   return (ps @ ps', e)
                                 else 
                                   fail "Pattern has %d fields, expected %d" (List.length ps) n 
    | (PVar :: ps', e) -> return (replicate PWild n @ ps', rebind u e)
    | (PWild :: ps', e) -> return (replicate PWild n @ ps', e)
    | (_ :: ps', e) -> fail "Expected tuple pattern"
    | ([], e) -> assert false
  in 
  Context.Seq.list (List.map split arms)

let split_sum u cs arms = 
  let open List in 
  let split = function
    | (PCon(c, p) :: ps, e) -> if mem c cs then
                                 return [c, (p :: ps, e)]
                               else
                                 fail "Constructor '%s' is not in the datatype" c 
    | (PWild :: ps, e) -> return (map (fun c -> (c, (PWild :: ps, e))) cs)
    | (PVar :: ps, e) -> return (map (fun c -> (c, (PWild :: ps, rebind u e))) cs)
    | (_ :: ps, e) -> fail "Expected constructor pattern"
    | ([], e) -> assert false
  in
  Context.Seq.list (List.map split arms) >>= fun branches -> 
  return (map (fun c -> (c, map snd (filter (fun (c', _) -> c = c') (concat branches)))) cs)
           
                   
let rec check (exp : exp) tp = 
  out exp >>= fun e -> 
  match e, tp  with 
  | Abs(x, _), _ -> assert false 
  | Num n, Int -> into (Num n)
  | Num _, tp -> expect "integer" tp 
  | Bool b, Bool -> into (Bool b)
  | Bool _, tp -> expect "boolean" tp 
  | If (e1, e2, e3), tp -> 
     (synth e1 >>= function
     | (e1', (Bool : tp)) -> check e2 tp >>= fun e2' -> 
                      check e3 tp >>= fun e3' -> 
                      into (If(e1', e2', e3'))
     | (e1', tp1) -> expect "boolean" tp1)
  | Lam (p, e2), Arrow(tp1, tp2) -> gensym "arg$" >>= fun u -> 
                                    invert [[p], e2] [u, tp1, Mono] tp2 >>= fun e2' -> 
                                    lam(u, e2')
  | Lam (p, e2), tp -> expect "function" tp 
  | Tuple es, Product tps -> 
     if List.length es = List.length tps then 
       List.map2 check es tps |> Context.Seq.list  >>= fun es' -> 
       into (Tuple es') 
     else 
       failwith "Tuple has wrong number of arguments"
  | Tuple es, tp -> expect "product" tp 
  | Con (c, e), Sum ctps -> 
     (match List.assoc c ctps with 
      | tp -> check e tp >>= fun e' -> into (Con(c, e'))
      | exception Not_found -> fail "constructor '%s' does not occur in type '%s'" c (print_type tp))
  | Con (c, e), tp -> expect "sum" tp 
  | Match (e, arms), tp -> synth e >>= fun (e', tp') ->
                           let cases = List.map (fun (p, e_arm) -> [p], e_arm) arms in
                           gensym "u$" >>= fun u -> 
                           invert cases [u, tp', Mono] tp >>= fun ebody' -> 
                           let_(u, e', ebody')
  | Singleton e, Set tp -> 
     check e tp >>= fun e' -> 
     into (Singleton e')
  | Singleton _, tp -> fail "Expected set type, got '%s'" (print_type tp)
  | Join (e1, e2), Set _ -> 
     check e1 tp >>= fun e1' -> 
     check e2 tp >>= fun e2' -> 
     into (Join(e1', e2'))
  | Join(_,_), tp -> fail "Expected set type, got '%s'" (print_type tp)
  | Box e1, Box tp1 ->  hidemono (check e1 tp1) >>= fun e1' -> 
                        into (Box e1')
  | Bind (p,e1,e2), Set _ ->
     (synth e1 >>= function
      | (e1', Set tp1) ->  gensym "u$" >>= fun u -> 
                           invert [[p], e2] [u, tp1, Mono] tp >>= fun e2' -> 
                           bind_ (u, e1', e2')
      | (e1', tp1) -> expect "set" tp1)
  | Bind (p,e1,e2), tp -> expect "set" tp 
  | _, tp -> synth exp >>= fun (e', tp') ->
             if tp = tp' then 
               return e' 
             else
               mismatch tp tp' 

and synth exp = 
  out exp >>= function 
  | Abs(_, _) -> assert false 
  | Num _ -> return (exp, Int)
  | Bool _ -> return (exp, (Bool : tp))
  | Op(op, e1, e2) -> 
     let (tp1, tp2, tp_res) = op_type op in
     check e1 tp1 >>= fun e1' -> 
     check e2 tp2 >>= fun e2' -> 
     into (Op(op, e1', e2')) >>= fun e' -> 
     return (e', tp_res)
  | App(e1, e2) -> 
     (synth e1 >>= function 
      | (e1', Arrow(tp2, tp)) -> check e2 tp2 >>= fun e2' -> 
                                 into (App(e1', e2')) >>= fun e_app' -> 
                                 return (e_app', tp)
      | (e1', tp) -> expect "function" tp)
  | Var x -> lookup x >>= fun (tp, tone) -> 
             into (Var x) >>= fun e_var -> 
             return (e_var, tp)
  | Annot(e, tp) -> check e tp >>= fun e' -> 
                    into (Annot(e', tp)) >>= fun e_annot -> 
                    return (e_annot, tp)
  | _ -> fail "Checking term in synthesizing position"             

and invert arms tps tp = 
  match arms, tps with
  | [], [] -> fail "Missing clauses"
  | ([], e) :: rest, [] -> check e tp 
  | ([], e) :: rest, tp :: tps -> assert false 
  | (p :: ps, e) :: rest, [] -> assert false 
  | arms, (u, tp, tone) :: tps' when leading_var arms -> 
     with_hyp (u, tp, tone) (invert (split_on_var u arms) tps' tp)
  | arms, (u, Product tps, tone) :: tps' -> 
     let n = List.length tps in 
     Context.Seq.list (replicate (gensym "u$") n) >>= fun us -> 
     split_tuple u n arms >>= fun arms' -> 
     let tps'' = (List.map2 (fun u tp -> u, tp, Mono) us tps) @ tps' in 
     with_hyp (u, Product tps, tone) (invert arms' tps'' tp) >>= fun ebody -> 
     let_tuple us (Ast.into (loc ebody) (Var u)) ebody
  | arms, (u, Sum ctps, tone) :: tps' -> 
     let (cs, tps) = List.split ctps in 
     Context.Seq.list (replicate (gensym "u$") (List.length cs)) >>= fun us ->
     split_sum u cs arms >>= fun carms -> 
     with_hyp (u, Sum ctps, tone) 
              (Context.Seq.list 
                 ((List.combine carms (List.combine us tps))
                  |> List.map (fun ((c, arms), (u_i, tp_i)) -> 
                                 invert arms ((u_i, tp_i, tone) :: tps') tp >>= fun e -> 
                                 return (c, e)))) >>= fun ces -> 
     into (Var u) >>= fun u_exp -> 
     into (Case(u_exp, ces))
  | arms, (u, tp', tone) :: tps' -> 
     fail "Expected leading variable pattern for type %s" (print_type tp')

                              
                             


     
