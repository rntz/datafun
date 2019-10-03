(* Strings with a unique identifier and a derivative degree. The "derivative
   degree" makes it easy, given a variable, to make up a variable standing for
   its derivative. This is kind of a hack, but the alternatives are:

   1. Passing contexts mapping variables to their derivative variables; or
   2. weak hashtable magic; or
   3. functorizing everything over the type of symbols/variables.

   All of which seem like more trouble than they're worth.
 *)
type t = {name: string; id: int; degree: int}
let compare = compare           (* export a suitable comparison operator *)
let name x = x.name
(* The variable signifying another variable's derivative. *)
let d x = {name = x.name; id = x.id; degree = 1+x.degree}

(* Generating fresh symbols *)
let next_id = ref 0
let nextId () = let x = !next_id in next_id := x + 1; x
(* Precondition: name is nonempty and does not begin with a numeral. *)
let fresh name =
  if name = "" then raise (Failure "Cannot create symbol with empty name")
  else if String.contains "0123456789" name.[0]
  then raise (Failure "Cannot create symbol whose name starts with a digit.")
  else {name = name; id = nextId(); degree = 0}

(* Generating interned symbols *)
let table: (string, t) Hashtbl.t = Hashtbl.create ~random:true 10
let intern name =
  try Hashtbl.find table name
  with Not_found -> let sym = fresh name in
                    Hashtbl.add table name sym; sym

(* to_string is injective over syms generated through the Sym interface,
 * although not over all possible syms. In particular, it relies on the
 * invariant that x.id = y.id implies x.name = y.name, (although not
 * x.degree = y.degree).
 *)
let to_string x =
  let d = match x.degree with
    | 0 -> "" | 1 -> "d" | d -> "d" ^ string_of_int d
  in Printf.sprintf "%s%s_%i" d x.name x.id
