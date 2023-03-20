Require Import String.
Require Import List.

(* CST term *)
Module Cst.
Inductive obj : Set :=
  | typ : nat -> obj
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | app : obj -> obj -> obj
  | fn : string -> obj -> obj -> obj
  | pi : string -> obj -> obj -> obj
  | var : string -> obj.
End Cst.

(* AST term *)
Inductive exp : Set :=
  (* Natural numbers *)
  | zero : exp
  | succ : exp -> exp
  (* Type constructors *)
  | nat : exp
  | typ : nat -> exp
  | var : nat -> exp
  (* Functions *)
  | fn : exp -> exp
  | app : exp -> exp -> exp
  (* Substitutions *)
  | sub : exp -> subst -> exp
with subst : Set :=
  | id : subst
  | weaken : subst
  | compose : subst -> subst -> subst
  | extend : subst -> exp -> subst.

(* Some convenient infix notations *)
Infix "∘" := compose (at level 70).
Infix "," := extend (at level 80).

Notation Ctx := (list exp).
