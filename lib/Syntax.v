Require Import String.

Module Cst.
Inductive obj :=
  | TType : nat -> obj
  | Nat : obj
  | Zero : obj
  | Succ : obj -> obj
  | App : obj -> obj -> obj
  | Fun : string -> obj -> obj -> obj
  | Pi : string -> obj -> obj -> obj
  | Var : string -> obj.
End Cst.
