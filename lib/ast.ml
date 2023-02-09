type term =
  | AType of int (* Type i *)
  | ANat (* Nat *)
  | AVar of int (* x *)
  | AZero (* zero *)
  | ASucc of term (* succ x *)
  | AFun of term (* fun x.M *)
  | AApp of term * term (* M N *)
  (* There's a couple more *)

  
  
