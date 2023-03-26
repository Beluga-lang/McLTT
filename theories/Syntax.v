Require Import String.
Require Import List.

(* CST term *)
Module Cst.
Inductive obj : Set :=
  | c_typ : nat -> obj
  | c_nat : obj
  | c_zero : obj
  | c_succ : obj -> obj
  | c_app : obj -> obj -> obj
  | c_fn : string -> obj -> obj -> obj
  | c_pi : string -> obj -> obj -> obj
  | c_var : string -> obj.
End Cst.

(* AST term *)
Inductive exp : Set :=
  (* Natural numbers *)
  | a_zero : exp
  | a_succ : exp -> exp
  (* Type constructors *)
  | a_nat : exp
  | a_typ : nat -> exp
  | a_var : nat -> exp
  (* Functions *)
  | a_fn : exp -> exp -> exp
  | a_app : exp -> exp -> exp
  (* Substitutions *)
  | a_sub : exp -> subst -> exp
with subst : Set :=
  | a_id : subst
  | a_weaken : subst
  | a_compose : subst -> subst -> subst
  | a_extend : subst -> exp -> subst.

(* Some convenient infix notations *)
Infix "∘" := a_compose (at level 70).
Infix "," := a_extend (at level 80).

Notation Ctx := (list exp).
