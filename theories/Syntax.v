Require Import String.
Require Import List.

Declare Scope mcltt.
Open Scope mcltt.

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
  | rec :  obj -> obj -> obj -> obj -> obj                           
  | var : string -> obj.
End Cst.

(* AST term *)
Inductive exp : Set :=
  (* Natural numbers *)
  | a_zero : exp
  | a_succ : exp -> exp
  | a_rec : exp -> exp -> exp -> exp -> exp                 
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
Infix "∙" := a_compose (at level 70) : mcltt.
Infix ",," := a_extend (at level 80) : mcltt.


Notation Ctx := (list exp).
Notation Sb := subst.
Notation Typ := exp.
Notation typ := a_typ.
Notation ℕ := a_nat.
Notation 𝝺 := a_fn.
Notation Π := a_pi.
Notation "x ⟦ σ ⟧" := (a_sub x σ) (at level 90, σ at next level) : mcltt.
Notation "'var_wk' σ" := (σ ∙ a_weaken ,, a_var 0) (at level 70, σ at next level) : mcltt.
Notation "x ⟦| σ ⟧" := (a_sub x (a_id,,σ)) (at level 90, σ at next level) : mcltt.
Notation "'sb_proj' σ" := (a_weaken ∙ σ) (at level 70, σ at next level) : mcltt.
Notation "M $ N" := (a_app M N) (at level 80, N at next level) : mcltt.
