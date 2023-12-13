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

Fixpoint nat_to_exp n : exp :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.
Definition num_to_exp n := nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat e : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.
Definition exp_to_num e :=
  match exp_to_nat e with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.

Declare Custom Entry exp.
Declare Scope exp_scope.
Delimit Scope exp_scope with exp.

Notation "{{ e }}" := e (at level 0, e custom exp at level 99) : exp_scope.
Notation "( x )" := x (in custom exp at level 0, x custom exp at level 99) : exp_scope.
Notation "~{ x }" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "e [ s ]" := (a_sub e s) (in custom exp at level 0, s custom exp at level 99) : exp_scope.
Notation "'λ' T e" := (a_fn T e) (in custom exp at level 0, T custom exp at level 30, e custom exp at level 30) : exp_scope.
Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : exp_scope.
Notation "'ℕ'" := a_nat (in custom exp) : exp_scope.
Notation "'Type(' n ')'" := (a_typ n) (in custom exp at level 0, n constr at level 99) : exp_scope.
Notation "'Π' T S" := (a_pi T S) (in custom exp at level 0, T custom exp at level 30, S custom exp at level 30) : exp_scope.
Number Notation exp num_to_exp exp_to_num : exp_scope.
Notation "'suc' e" := (a_succ e) (in custom exp at level 30, e custom exp at level 30) : exp_scope.
Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0) : exp_scope.
Notation "'$id'" := a_id (in custom exp at level 0) : exp_scope.
Notation "'$wk'" := a_weaken (in custom exp at level 0) : exp_scope.
Infix "∙" := a_compose (in custom exp at level 70) : exp_scope.
Infix "," := a_extend (in custom exp at level 80) : exp_scope.

Notation Ctx := (list exp).
Notation Sb := subst.
Notation Typ := exp.
Notation typ := a_typ.
Notation ℕ := a_nat.
Notation 𝝺 := a_fn.
Notation Π := a_pi.
