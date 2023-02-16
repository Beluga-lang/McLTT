open Cst
open Ast

exception Unbound_variable of string

  

let find_var (s : string) (ctx : string list) : int  =
  let rec find s ctx (index : int) : int =
  match ctx with
  | [] -> raise (Unbound_variable s)
  | c::cs ->
     if c = s then
       index
     else
       find s cs (index+1)
  in
  find s ctx 0
 
let abstract o = 
  let rec abstract (o : obj) (ctx: string list) : term =
    match o with
    | Type n -> AType n
    | Nat -> ANat
    | Zero -> AZero
    | Succ o1 -> ASucc (abstract o1 ctx)
    | Var s -> AVar (find_var s ctx)
    | Fun (s, _, o1) -> AFun (abstract o1 (s :: ctx))
    | App (o1,o2) -> AApp (abstract o1 ctx, abstract o2 ctx)
    | _ -> failwith "TODO"
  in
  abstract o []
