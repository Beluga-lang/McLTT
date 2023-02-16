open Main
open Cst

let%test "type" = parse "Type 5" = Type 5
let%test "nat" = parse "Nat" = Nat
let%test "var" = parse "x" = Var "x"
let%test "zero" = parse "zero" = Zero
let%test "succ zero" = parse "succ zero" = Succ Zero
let%test "lambda" = parse "fun (x : Type 5).y" = Fun ("x", Type 5, Var "y")
let%test "application" = parse "(fun (x : Nat).x) Nat" = App (Fun ("x", Nat, Var "x"), Nat)
let%test "nested 1" = parse "(Type 5) zero" = App (Type 5, Zero)
let%test "nested 2" = parse "succ (succ (succ (succ zero)))" = Succ (Succ (Succ (Succ Zero)))
let%test "pi" = parse "pi (x:Nat).x" = Pi ("x", Nat, Var "x")

(* Some more finer details *)
let%test "pi missing colon" = parse "pi (x Nat).x" <> Pi ("x", Nat, Var "x")
let%test "ignore whitespace" = parse "fun (x  
                                     : Type 4).x" <> Pi ("x", Type 4, Var "x")
