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
  | a_zero : exp
  | a_succ : exp -> exp
  (* Type constructors *)
  | a_nat : exp
  | a_typ : nat -> exp
  | a_var : nat -> exp
  (* Functions *)
  | a_fn : exp -> exp -> exp
  | a_app : exp -> exp -> exp
  | a_pi : exp -> exp -> exp
  (* Substitutions *)
  | a_sub : exp -> subst -> exp
with subst : Set :=
  | a_id : subst
  | a_weaken : subst
  | a_compose : subst -> subst -> subst
  | a_extend : subst -> exp -> subst.

(* Some convenient infix notations *)
Infix "∙" := a_compose (at level 70).
Infix ",," := a_extend (at level 80).


Notation Ctx := (list exp).
Notation Sb := subst.
Notation Typ := exp.
Notation typ := a_typ.
Notation ℕ := a_nat.
Notation 𝝺 := a_fn.
Notation Π := a_pi.
