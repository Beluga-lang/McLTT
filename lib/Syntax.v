Require Import String.
Require Import List.

(* CST term *)
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

(* AST term *)
Inductive exp : Set :=
  (* Natural numbers *)
  | Zero : exp
  | Succ : exp
  (* Type constructors *)
  | Nat : exp
  | Typ : nat -> exp
  | Var : nat -> exp
  (* Functions *)
  | Fun : exp -> exp
  | App : exp -> exp -> exp
  (* Substitutions *)
  | Sub : exp -> subst -> exp
with subst : Set :=
  | Id : subst
  | Weaken : subst
  | Compose : subst -> subst -> subst
  | Extend : subst -> exp -> subst.

Definition Ctx : Set := list exp.
