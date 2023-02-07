open Main
open Cst

let%test "type" = parse "Type 5" = Type 5
let%test "nat" = parse "Nat" = Nat
let%test "var" = parse "x" = Var "x"
let%test "zero" = parse "zero" = Zero
let%test "succ zero" = parse "succ zero" = Succ Zero
let%test "lambda" = parse "fun x.y" = Fun ("x", Var "y")
let%test "application" = parse "(fun x.x) Nat" = App (Fun ("x", Var "x"), Nat)
let%test "nested 1" = parse "(Type 5) zero" = App (Type 5, Zero)
let%test "nested 2" = parse "succ (succ (succ (succ zero)))" = Succ (Succ (Succ (Succ Zero)))
