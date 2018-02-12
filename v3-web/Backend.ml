open Ast

(* type pointed =
 *   [ `Bool | `Set | `Tuple of pointed list ] *)

type semilat =
  [ `Bool | `Set
  | `Tuple of semilat list
  | `Func of semilat ]

type equal =
  [ `Base of base
  | `Set of equal
  | `Tuple of equal list
  | `Sum of (tag * equal) list ]

module type BACKEND = sig

  type var
  type exp
  type expFun = string * (var -> exp)

  (* There is a problem with my clever scheme:
   * how can I get debruijn indices out of this?
   * or even avoid alpha-conflicts except via global gensym?
   * maybe global gensym is the solution.
   * but that doesn't help if I'm writing an interpreter!
   *)

  (* BIGGER PROBLEM:
   *
   * patterns in Ast.ml allow nonlinearity, with "test equality" semantics!
   * but I don't want this to be the semantics in the backend;
   * the type-checker is the bit that handles nonlinearity-as-equality.
   * fix this.
   *)
  type pattern =
    (* shit, how does the scoping for PatEq work?
     * in e.g. PatTuple [PatVar "x", PatEq (var "x")]
     * this seems wrong. *)
    | PatEq of exp
    | PatWild | PatVar of var
    | PatWhere of pattern * exp
    | PatTuple of pattern list | PatTag of tag * pattern

  (* Basic forms *)
  (* give both debruijn index and name of variable *)
  val var: int * var -> exp
  val lit: lit -> exp

  val stuck: string -> exp        (* unrecoverable error *)
  val bind: exp -> expFun -> exp
  val fix: exp -> expFun -> exp

  (* TODO: primitive functions? *)
  (* our typeclasses *)
  val eq: equal -> exp -> exp -> exp
  val lub: semilat -> exp list -> exp
  (* val point: pointed -> exp *)

  (* introductions *)
  val tuple: exp list -> exp
  val tag: tag -> exp -> exp
  val mkSet: exp list -> exp

  (* eliminators *)
  val app: exp -> exp -> exp
  val ifThenElse: exp -> exp -> exp -> exp
  val forSet: semilat -> exp -> string * (var -> exp) -> exp
  (* destruct subject (pat, matchCase) failCase *)
  val destruct: exp -> pat * (var list -> exp) -> exp -> exp
  val destructOrDie: exp -> pat * (var list -> exp) -> exp

end
