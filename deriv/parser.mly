%{
open Base
open Ast

let getpos () = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let rangepos n m = (Parsing.rhs_start_pos n, Parsing.rhs_end_pos m)

let product = function
   | [] -> Product []
   | [p] -> p
   | tp :: tps -> Product (tp :: tps)

let ptuple = function
   | [] -> PTuple []
   | [p] -> p
   | p :: ps -> PTuple (p :: ps)


let pos (p, _) = p 

(*    

let rec make_fun(pos, ps, e) =
  match ps with
  | [] -> e
  | p :: ps -> (pos, ELam(p, make_fun(pos, ps, e)))

let rec make_app(f, args) =
  match args with
  | [] -> f
  | e :: es -> (merge(pos f, pos e), EApp(make_app(f, es), e))

let make_decl_list decls body =
  List.fold_left
    (fun acc (loc, x, term, tp) -> (pos term, ELet((loc, PVar x), (pos term, EAnnot(term, tp)), acc)))
    body
    decls

let make_pure_decl_list decls body =
  List.fold_left
    (fun acc (ppos, x, term, tp) ->
      let annot (e, tp) = (pos term, EAnnot(e, tp)) in 
      let elet(p, e1, e2) = (pos term, ELet(p, e1, e2)) in
      let bang e = (pos term, EBang e) in
      let pbang x = (ppos, PBang x) in 
      elet(pbang x, annot(bang term, Pure tp), acc))
    body
    decls
*)

%}
%token OF 
%token DOT 
%token VAL
%token REC 
%token RPAREN
%token LPAREN
%token RBRACE
%token LBRACE
%token RBRACK
%token LBRACK
%token COMMA
%token UNDERSCORE
%token BOX
%token FUN
%token TO
%token PLUS
%token MINUS
%token AST
%token ANDAND
%token OR
%token LET
%token COLON
%token EQUAL
%token LT
%token LEQ
%token GT
%token GEQ 
%token IN
%token FIX
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token INT
%token AND
%token BOOL
%token UNIT
%token MATCH
%token WITH
%token BEGIN
%token END
%token SET 
%token BAR 
%token DOUBLECOLON 
%token <string> CONID
%token <float> NUM 
%token <string> STRING 
%token <string> IDENT 
%token EOF



%nonassoc IN
%nonassoc THEN ELSE
%nonassoc IF
%nonassoc LET 
%right CONS 
%left COLON
%right DOUBLECOLON
%right OR 
%right ANDAND
%left EQUAL LT LEQ GEQ GT 
%left PLUS MINUS
%left TIMES  




%type <Ast.tp> tp 
%type <Ast.tp> test_tp 

%type <Ast.pat * Ast.var list> pat
%type <Ast.pat * Ast.var list> test_pat

/*
%type <Ast.exp> exp
%type <Ast.decl> toplevel_decl
%type <Ast.program> program 
%type <Ast.signature> signature
%type <Ast.signature_elt> signature_decl

%type <Ast.exp> test_exp 
%type <Ast.decl> test_toplevel_decl
%type <Ast.program> test_program
%type <Ast.signature> test_signature
%type <Ast.signature_elt> test_signature_decl
*/

%start tp test_tp pat test_pat /* test_exp test_toplevel_decl test_program test_signature test_signature_decl tp pat exp toplevel_decl program signature signature_decl */


%%



/* Syntax of types */

tp_atom :
  UNIT                      { Product [] }
| INT         	            { Int }
| BOOL            	    { Bool }
| STRING         	    { String }
| LPAREN tp RPAREN          { $2 }
| LBRACK ctps RBRACK        { Sum $2 }            
;

ctps :
                          { [] }   
| CONID COLON tp          { [$1, $3] }
| CONID COLON tp BAR ctps { ($1, $3) :: $5 }
;

tp_app :
| tp_atom                { $1 }
| BOX tp_atom      	 { Box $2 }
| SET tp_atom	         { Set $2 }
;

and_tps :
   tp_app                 { [$1] }
|  AND tp_app and_tps     { $2 :: $3 }
;

product_tp : 
  and_tps                 { product $1 }
;

tp :
| product_tp                  { $1 }
| product_tp TO tp            { Arrow($1, $3) }
;

/* Syntax of patterns */

pat_atom : 
  IDENT              { (PVar, [$1]) }
| TRUE               { (PBool true, []) }
| FALSE              { (PBool false, []) }
| LPAREN comma_pat RPAREN  { let (ps, xs) = $2 in (ptuple ps, xs) }
;

pat_app : 
  pat_atom           { $1 }
| BOX pat_atom       { let (p, xs) = $2 in 
                       (PBox p, xs) }
| CONID pat_atom     { let (p, xs) = $2 in 
                       (PCon($1, p), xs) }
;

comma_pat :
  pat_app                  { let (p, xs) = $1 in ([p], xs) }
| pat_app COMMA comma_pat  { let (p, xs) = $1 in 
                             let (ps, ys) = $3 in
                             (p :: ps, xs @ ys) }
;

pat :
  pat_atom                { $1 }
;

test_tp : tp EOF {$1};
test_pat : pat EOF {$1};

