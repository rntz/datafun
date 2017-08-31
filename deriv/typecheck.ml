open Ast
open Util 
open Context

let lam (u, e) = into (Abs(u, e)) >>= fun e' -> 
                 into (Lam(PVar, e'))

let let_ (x, e1, e2) = into (Abs(x, e2)) >>= fun e2' -> 
                       into (Case(e1, [PVar, e2']))

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


let rec find_var = function
  | [] -> None 
  | ((PVar :: ps), Abs(u, e)) :: arms -> Some u 
  | ((PVar :: ps), e) :: arms -> assert false 
  | arm :: arms -> find_var arms 

  
                           
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
  | Lam (p, e2), Arrow(tp1, tp2) -> (invert [[p], e2] [tp1] tp2 >>= function 
                                     | [u], e' -> lam(u, e')
                                     | us, e' -> assert false)
  | Lam (p, e2), tp -> expect "function" tp 
  | Tuple es, Product tps -> 
     if List.length es = List.length tps then 
       Context.Seq.list (List.map2 check es tps) >>= fun es' -> 
       into (Tuple es') 
     else 
       failwith "Tuple has wrong number of arguments"
  | Tuple es, tp -> expect "product" tp 
  | Con (c, e), Sum ctps -> 
     (match List.assoc c ctps with 
      | tp -> check e tp >>= fun e' -> into (Con(c, e'))
      | exception Not_found -> fail "constructor '%s' does not occur in type '%s'" c (print_type tp))
  | Con (c, e), tp -> expect "sum" tp 
  | Case (e, arms), tp -> (synth e >>= fun (e', tp') ->
                           let cases : (Ast.pat list * Ast.exp) list = List.map (fun (p, e_arm) -> [p], e_arm) arms in
                           invert cases [tp'] tp >>= function
                           | [u], ebody' -> into (Abs(u, ebody')) >>= fun ebody' -> 
                                            into (Case(e', [PVar, ebody']))
                           | us, ebody -> assert false)
  | Singleton e, Set tp -> 
     check e tp >>= fun e' -> 
     into (Singleton e')
  | Singleton _, tp -> fail "Expected set type, got '%s'" (print_type tp)
  | Join (e1, e2), Set _ -> 
     check e1 tp >>= fun e1' -> 
     check e2 tp >>= fun e2' -> 
     into (Join(e1', e2'))
  | Join(_,_), tp -> fail "Expected set type, got '%s'" (print_type tp)
  | Bind (p,e1,e2), Set _ ->
     (synth e1 >>= function
      | (e1', Set tp1) -> (invert [[p], e2] [tp1] tp >>= function
                           | [u], e2' -> let_ (u, e1', e2')
                           | us, e2' -> assert false)
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
  | ([], e) :: rest, [] -> check e tp >>= fun e' -> 
                           return ([], e')
  | arms, (Arrow(_, _) as tp) :: tps' -> split_var arms >>= fun (u, arms') -> 
                                         invert arms' tps' >>= fun (us, ebody) -> 
                                         return (u :: us, ebody)
  | arms, tp :: tps' when leading_var arms -> split_var arms >>= fun (u, arms') -> 
                                              invert arms' tps' >>= fun (us, ebody) -> 
                                              return (u :: us, ebody)
  | 
