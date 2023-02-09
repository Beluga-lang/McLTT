type obj =
  | Type of int (* Type i *)
  | Nat (* Nat *)
  | Var of string (* x *)
  | Zero (* zero *)
  | Succ of obj (* succ x *)
  | Fun of string * obj (* fun x.M *)
  | App of obj * obj (* M N *)
  (* There's a couple more *)

type term =
  | Type of int (* Type i *)
  | Nat (* Nat *)
  | Var of string (* x *)
  | Zero (* zero *)
  | Succ of obj (* succ x *)
  | Fun of int * obj (* fun x.M *)
  | App of obj * obj (* M N *)
  (* There's a couple more *)
