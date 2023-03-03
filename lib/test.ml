(* Unit test cases for parsing *)

open Main
open Parser.Cst

let x, y, z = ['x'], ['y'], ['z']

let%test "type" = parse "Type 5" = Some (TType 5)
let%test "nat" = parse "Nat" = Some Nat
let%test "var" = parse "x" = Some (Var x)
let%test "zero" = parse "zero" = Some (Zero)
let%test "succ zero" = parse "succ zero" = Some (Succ Zero)
let%test "lambda" = parse "fun (x : Type 5).y" = Some (Fun (x, TType 5, Var y))
let%test "lambda multiple args" = parse "fun (x : Nat) (y : Nat) . x" = Some (Fun (x, Nat, Fun (y, Nat, Var x)))
let%test "lambda multiple args 2" = parse "fun (x : Nat) (y : Nat) (z : Nat) . z" = Some (Fun (x, Nat, Fun (y, Nat, Fun (z, Nat, Var z))))
let%test "application" = parse "(fun (x : Nat).x) Nat" = Some (App (Fun (x, Nat, Var x), Nat))
let%test "nested 1" = parse "(Type 5) zero" = Some (App (TType 5, Zero))
let%test "nested 2" = parse "succ (succ (succ (succ zero)))" = Some (Succ (Succ (Succ (Succ Zero))))
let%test "pi" = parse "pi (x:Nat).x" = Some (Pi (x, Nat, Var x))
let%test "pi multiple args" = parse "pi (x : Nat) (y : Nat) (z : Nat) . z" = Some (Pi (x, Nat, Pi (y, Nat, Pi (z, Nat, Var z))))

(* Some more finer details *)

let%test "pi missing colon" = parse "pi (x Nat).x" = None

let%test "ignore whitespace" = parse "fun (x  
                                     : Type 4).x" = Some (Fun (x, TType 4, Var x))
