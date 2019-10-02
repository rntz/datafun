(* Strings with a unique identifier and a derivative degree. The "derivative
   degree" makes it easy, given a variable, to make up a variable standing for
   its derivative. This is kind of a hack, but the alternatives are:

   1. Passing contexts mapping variables to their derivative variables; or
   2. weak hashtable magic; or
   3. functorizing everything over the type of symbols/variables.

   All of which seem like more trouble than they're worth.
 *)
open Util
type t = sym
let compare = compare           (* export the right comparison operator *)
let next_id = ref 0
let nextId () = let x = !next_id in next_id := x + 1; x
let gen name = {name = name; id = nextId(); degree = 0}
(* it is important that the `d` function be deterministic *)
let d x = {name = x.name; id = x.id; degree = 1+x.degree}

(* to_uid is injective over syms generated through the Sym interface, although
 * not over all possible syms. In particular, it relies on the invariant that
 * x.id = y.id implies x.name = y.name, (although not x.degree = y.degree).
 *
 * In principle I could use the module system to enforce this interface,
 * but for ease of debugging I do not. *)
let to_uid x =
  let d = match x.degree with
    | 0 -> "" | 1 -> "d" | d -> "d" ^ string_of_int d
  in Printf.sprintf "%s%s_%i" d x.name x.id

(* Yields a hopefully human-friendly name. For now just use to_uid. *)
let to_string = to_uid
