open Util open Lang open Passes

(* Putting it all together. *)
let x = Sym.gen "x" let y = Sym.gen "y"
let a = Sym.gen "a" let b = Sym.gen "b"
let x1 = Sym.gen "x1" let x2 = Sym.gen "x2"
let y1 = Sym.gen "y1" let y2 = Sym.gen "y2"
let path = Sym.gen "path"
let edge = Sym.gen "edge"
let trans = Sym.gen "trans"
let r = Sym.gen "r" and r1 = Sym.gen "r1" and r2 = Sym.gen "r2"
let s = Sym.gen "s"
let i = Sym.gen "i" and j = Sym.gen "j" and k = Sym.gen "k"
let self = Sym.gen "self"

module Examples(Modal: MODAL) = struct
  module Lang = Typecheck(Modal)
  open Lang

  type test = Modal.term
  let testIn (tp: tp) cx (ex: term): Modal.term =
    ex (cx |> List.map (fun (a,b,c) -> a,(b,c)) |> Cx.from_list) tp
  let test (tp: tp) (ex: term) = ex Cx.empty tp

  let shouldFail f = try ignore (f ()); impossible "shouldn't typecheck"
                     with TypeError _ -> ()
  let _ = shouldFail (fun _ -> testIn `Bool [x,Hidden,`Bool] (expr (var x)))

  (* TODO: more tests. *)
  let t0 = testIn `Bool [x,Id,`Bool] (expr (var x))
  let t1 = testIn `Bool [x,Box,`Bool] (expr (var x))
  (* t2 = λx.x *)
  let t2 = test (`Fn(`Bool,`Bool)) (lam x (expr (var x)))
  let t3 = testIn `Bool
             [x,Id,`Fn(`Bool,`Bool); y,Id,`Bool]
             (expr (app (var x) (expr (var y))))

  let t4 = test (`Box (`Fn(`Bool, `Bool)))
             (box (lam x (expr (var x))))

  let term5 = letBox x
                (asc (`Box (`Fn(`Bool, `Bool)))
                   (box (lam x (expr (var x)))))
                (expr (app (var x) (expr (var y))))
  let t5 = testIn `Bool [y,Id,`Bool] term5

  let t6 = test (`Tuple []) (fix x (expr (var x)))

  (* Relation composition *)
  let strel: tp = `Set (`Tuple [`String; `String])
  let t7 = testIn strel [a,Id,strel;b,Id,strel]
             (forIn x (var a)
                (forIn y (var b)
                   (guard (expr (equals (proj 1 (var x)) (proj 0 (var y))))
                      (set [tuple [expr (proj 0 (var x));
                                   expr (proj 1 (var y))]]))))

  (* Intersection *)
  let strset: tp = `Set `String
  let t8 = testIn strset [a,Id,strset; b,Id,strset]
             (forIn x (var a)
                (forIn y (var b)
                   (guard (expr (equals (var x) (var y)))
                      (set [expr (var x)]))))

  (* Test for letBox at first-order type.
   * Should optimize derivative to False. *)
  let t9 = testIn `Bool [x,Id,`Box `Bool]
             (letBox y (var x) (expr (var y)))

  (* Transitive closure *)
  let t10 = testIn strel [edge, Box, strel]
          (fix path (union [expr (var edge);
                            forIn a (var edge)
                              (forIn b (var path)
                                 (guard (expr (equals (proj 1 (var a)) (proj 0 (var b))))
                                    (set [tuple [expr (proj 0 (var a));
                                                 expr (proj 1 (var b))]])))]))

  (* TODO: regular expressions.
   * I'll eventually need arithmetic for this! *)
  let lamBox x e = let xtmp = Sym.gen x.name in
                   lam xtmp (letBox x (var xtmp) e)
  let tnat = `String
  let tchar = `String
  let tstring =  `Set (`Tuple [tnat; tchar])
  let natrel = `Set (`Tuple [tnat; tnat])
  let tregex = `Fn (`Box tstring, natrel)

  let t11rplus =
    testIn
      (`Fn (`Box tregex, tregex))
      [trans, Box, `Fn(`Box natrel, natrel)]
      (* λ[r] [s]. trans [r [s]] *)
      (lamBox r (lamBox s (expr (app (var trans)
                                   (box (expr (app (var r) (box (expr (var s))))))))))

  let mkTrans (edge: sym) =
    (fix path (union [expr (var edge);
                      forIn a (var edge)
                        (forIn b (var path)
                           (guard (expr (equals (proj 1 (var a)) (proj 0 (var b))))
                              (set [tuple [expr (proj 0 (var a));
                                           expr (proj 1 (var b))]])))]))

  (* Explicitly inlining transitive closure into regex star. *)
  let t12rplus =
    testIn (`Fn (`Box tregex, tregex))
      []
      (* λ[r] [s]. let edges = [r [s]] in trans edges *)
      (lamBox r
         (lamBox s
            (letBox edge (asc (`Box natrel) (box (expr (app (var r) (box (expr (var s)))))))
               (mkTrans edge))))

(* 12 generates:

\r_18. let (r_11, dr_11) = r_18 in
\s_17. let (s_14, ds_14) = s_17 in
let (edge_9, dedge_9) = ((r_11 (s_14, Set.empty)), Set.empty) in
semifix
 ((\path_8. (union edge_9 (forIn edge_9 (\a_2. (forIn path_8 (\b_3. (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))),
  \path. \dpath.
    for (a in edge_9, b in dpath, snd a == fst b)
       {(fst a, snd b)})

 *)

  let tregex2 = `Fn(`Box tstring, `Fn (`Box tnat, `Set tnat))
  let t13rstar =
    testIn (`Fn (`Box tregex2, tregex2))
      []
      (* λ[r] [s] [i]. fix self is {i} ∪ for (j ∈ self) r [s] [j] *)
      (lamBox r
         (lamBox s
            (lamBox i
               (fix self
                  (union [ set [expr (var i)]
                         ; forIn j (var self)
                             (expr (app (app (var r) (box (expr (var s)))) (box (expr (var j)))))
         ])))))

(* 13 generates:

\r_25. let (r_11, dr_11) = r_25 in
\s_24. (let (s_14, ds_14) = s_24 in
\i_23. (let (i_15, di_15) = i_23 in
semifix
((\self_18. (union (set [i_15]) (forIn self_18 (\j_16. ((r_11 (s_14, Set.empty)) (j_16, ())))))),
 \self. \dself.
   for (j ∈ dself) r_11 (s_14, Set.empty) (j, ()))))

 *)

  let tests = [t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t10;t11rplus;t12rplus;t13rstar]
end

module Simplified = Passes.Simplify(ToHaskell)
module Zeroed = Passes.ZeroChange(Simplified)

(* fully optimized *)
module Debug = Examples(Seminaive(Zeroed))
let runTest (i: int) (x,y: Debug.test) =
  Printf.printf "%d: %s\n%d: %s\n"
    i (StringBuilder.finish (Simplified.finish (Zeroed.finish x)))
    i (StringBuilder.finish (Simplified.finish (Zeroed.finish y)))
let runTests () = List.iteri runTest Debug.tests

(*
OPTIMIZED t11rplus:

  \r. let (r, dr) = r in
  \s. let (s, ds) = s in
  trans (r (s, Set.empty), Set.empty)

BOTTOM-PROP ONLY t11rplus:

  \r. let (r, dr) = r in
  \s. let (s, ds) = s in
  trans (r (s, Set.empty), (dr (s, Set.empty) ()))

the zero-change optimization saves us a call to dr!

NAIVE/PASS-THROUGH t11rplus:

  \r. let r = r in \s. let s = s in trans (r s)

*)

(* only bottom prop, no zero-change analysis *)
module Debug2 = Examples(Seminaive(DummyZero(Simplified)))
let runTest2 (i: int) (x,y: Debug2.test) =
  Printf.printf "%d: %s\n%d: %s\n"
    i (StringBuilder.finish (Simplified.finish x))
    i (StringBuilder.finish (Simplified.finish y))
let runTests2 () = List.iteri runTest2 Debug2.tests

(* naive version *)
module Naive = Examples(DropBoxes(ToHaskell))
let runNaiveTest (i: int) (x: Naive.test) =
  Printf.printf "%d: %s\n" i (StringBuilder.finish x)
let runNaiveTests () = List.iteri runNaiveTest Naive.tests

(* 2019-07-01 Faster version of transitive closure:

semifix
(\path.
  edge ∪
  forIn (a in edge) for (b in path) when (snd a == fst b)
    {(fst a, snd b)}),
(\path dpath.
  for (a in edge) for (b in dpath) when (snd a == fst b)
    {(fst a, snd b)})

Which is what we wanted!
*)
