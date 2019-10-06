(* TODO: I'm not really sure when to use hov boxes & when to use normal ones. *)
open Util
open Type
(* type formatter = Format.formatter let fprintf = Format.fprintf *)
open Format

type tp = rawtp
(* A term takes a precdence level & a formatter and prints itself. *)
type term = int -> Format.formatter -> unit

let finish (term:term) (out: formatter): unit = fprintf out "@[<hov 0>%t@]" (term 0)

let tpstr = (Type.to_string :> tp -> string)

let paren f out = fprintf out "@[<hov 1>(@,%t@,)@]" f
let brace f out = fprintf out "@[<hov 1>{@,%t@,}@]" f

let at myPrec f (envPrec: int) (out: formatter) =
  if envPrec <= myPrec then fprintf out "@[<hov 0>%t@]" f else paren f out

let var _ x (_prec: int) (out: formatter) = fprintf out "%s" (Sym.name x)

let letIn (a: tp) _b x expr body =
  at 0 (fun out -> fprintf out "let %s: %s =@ %t@ in@ %t"
                     (Sym.name x) (tpstr a) (expr 0) (body 0))
  
let commaspace out () = fprintf out ",@ "
let commasep (terms: term list) (out: formatter) =
  pp_print_list ~pp_sep:commaspace (fun out term -> term 2 out) out terms

let lam _a _b x body =
  at 0 (fun out -> fprintf out "\\%s.@ %t" (Sym.name x) (body 0))

let apply fnc arg = at 3 (fun out -> fprintf out "@[<hov 1>%t@ %t@]" (fnc 3) (arg 4))
let app _ _ fnc arg = apply fnc arg

let tuple tpterms = at 1 (commasep (List.map snd tpterms))
let proj _ = todo "proj"
let letTuple (tpxs: (tp * sym) list) _tp expr body =
  at 0 (fun out -> fprintf out "let (%s) =@ %t@ in@ %t"
                     (String.concat "," (List.map (fun (_,x) -> Sym.name x) tpxs))
                     (expr 0) (body 0))

let string s _ out = fprintf out "%S" s
let bool b _ out = fprintf out "%B" b
let nat n _ out = fprintf out "%i" n
let ifThenElse _ = todo "ifThenElse"
let guard _lat cnd thn =
  at 0 (fun out -> fprintf out "when %t do@ %t" (cnd 0) (thn 0))

let set _a terms _prec = brace (commasep terms)

(* TODO: several options here.
 * - should I print the types of "empty" unions?
 * - should I indicate singleton unions?
 *)
let _latstr2 = (Type.to_string2 :> tp semilat -> string)
let empty (_lat: tp semilat) _prec out = fprintf out "empty"
  (* fprintf out "empty%@%s" (latstr2 lat) *)
let union (lat: tp semilat): term list -> term = function
  | [] -> empty lat
  | [term] -> term
  (* | [term] -> at 1 (fun out -> fprintf out "or %t" (term 2)) *)
  | terms ->
     let orspace out () = fprintf out "@ or@ " in
     let f out term = term 2 out in
     at 1 (fun out -> pp_print_list ~pp_sep:orspace f out terms)

let forIn _a _lat x expr body =
  at 0 (fun out -> fprintf out "for %s in %t do@ %t"
                     (Sym.name x) (expr 0) (body 0))

let fix _ = todo "fix"
let equals _tp e1 e2 = at 2 (fun out -> fprintf out "%t@ = %t" (e1 3) (e2 3))
let semifix _lat body = apply (fun _ out -> fprintf out "semifix") body
