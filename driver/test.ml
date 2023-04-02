(* Unit test cases for parsing *)

open Main
open Parser.Cst

let x, y, z = ("x", "y", "z")

let%test "type" = parse "Type 5" = Some (Coq_typ 5)
let%test "nat" = parse "Nat" = Some Coq_nat
let%test "var" = parse "x" = Some (Coq_var x)
let%test "zero" = parse "zero" = Some Coq_zero
let%test "succ zero" = parse "succ zero" = Some (Coq_succ Coq_zero)

let%test "lambda" =
  parse "fun (x : Type 5).y" = Some (Coq_fn (x, Coq_typ 5, Coq_var y))

let%test "lambda multiple args" =
  parse "fun (x : Nat) (y : Nat) . x"
  = Some (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_var x)))

let%test "lambda multiple args 2" =
  parse "fun (x : Nat) (y : Nat) (z : Nat) . z"
  = Some
      (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_fn (z, Coq_nat, Coq_var z))))

let%test "application" =
  parse "(fun (x : Nat).x) Nat"
  = Some (Coq_app (Coq_fn (x, Coq_nat, Coq_var x), Coq_nat))

let%test "nested 1" =
  parse "(Type 5) zero" = Some (Coq_app (Coq_typ 5, Coq_zero))

let%test "nested 2" =
  parse "succ (succ (succ (succ zero)))"
  = Some (Coq_succ (Coq_succ (Coq_succ (Coq_succ Coq_zero))))

let%test "pi" = parse "pi (x:Nat).x" = Some (Coq_pi (x, Coq_nat, Coq_var x))

let%test "pi multiple args" =
  parse "pi (x : Nat) (y : Nat) (z : Nat) . z"
  = Some
      (Coq_pi (x, Coq_nat, Coq_pi (y, Coq_nat, Coq_pi (z, Coq_nat, Coq_var z))))

(* Some more finer details *)

let%test "pi missing colon" = parse "pi (x Nat).x" = None

let%test "ignore whitespace" =
  parse "fun (x  \n                                     : Type 4).x"
  = Some (Coq_fn (x, Coq_typ 4, Coq_var x))
