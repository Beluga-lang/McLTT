(* Unit test cases for parsing *)

open Main
open Cst

let%test "type" = parse "Type 5" = Type 5
let%test "nat" = parse "Nat" = Nat
let%test "var" = parse "x" = Var "x"
let%test "zero" = parse "zero" = Zero
let%test "succ zero" = parse "succ zero" = Succ Zero
let%test "lambda" = parse "fun (x : Type 5).y" = Fun ("x", Type 5, Var "y")
let%test "lambda multiple args" = parse "fun (x : Nat) (y : Nat) . x" = Fun ("x", Nat, Fun ("y", Nat, Var "x"))
let%test "lambda multiple args 2" = parse "fun (x : Nat) (y : Nat) (z : Nat) . z" = Fun ("x", Nat, Fun ("y", Nat, Fun ("z", Nat, Var "z")))
let%test "application" = parse "(fun (x : Nat).x) Nat" = App (Fun ("x", Nat, Var "x"), Nat)
let%test "nested 1" = parse "(Type 5) zero" = App (Type 5, Zero)
let%test "nested 2" = parse "succ (succ (succ (succ zero)))" = Succ (Succ (Succ (Succ Zero)))
let%test "pi" = parse "pi (x:Nat).x" = Pi ("x", Nat, Var "x")
let%test "pi multiple args" = parse "pi (x : Nat) (y : Nat) (z : Nat) . z" = Pi
("x", Nat, Pi ("y", Nat, Pi ("z", Nat, Var "z")))

(* Some more finer details *)

let%test "pi missing colon" =
  try let _ = parse "pi (x Nat).x" in false with
    _ -> true

let%test "ignore whitespace" = parse "fun (x  
                                     : Type 4).x" <> Pi ("x", Type 4, Var "x")
