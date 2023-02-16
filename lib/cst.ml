type obj =
  | Type of int (* Type i *)
  | Nat (* Nat *)
  | Var of string (* x *)
  | Zero (* zero *)
  | Succ of obj (* succ x *)
  | Fun of string * obj * obj (* fun (x:T).M *)
  | App of obj * obj (* M N *)
  | Pi of string * obj * obj (* pi (x:A).B *)
  (* There's a couple more *)

