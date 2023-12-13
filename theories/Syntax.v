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

Declare Custom Entry ast.
Declare Scope ast_scope.

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

Notation "{{ e }}" := e (at level 0, e custom ast at level 99) : ast_scope.
Notation "( x )" := x (in custom ast at level 0, x custom ast at level 99) : ast_scope.
Notation "~{ x }" := x (in custom ast at level 0, x constr at level 0) : ast_scope.
Notation "x" := x (in custom ast at level 0, x constr at level 0) : ast_scope.
Notation "e [ s ]" := (a_sub e s) (in custom ast at level 0) : ast_scope.
Notation "'λ' T -> e" := (a_fn T e) (in custom ast at level 0, e custom ast at level 99) : ast_scope.
Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom ast at level 20, f custom ast, x custom ast at level 9, y custom ast at level 9) : ast_scope.
Notation "'ℕ'" := a_nat (in custom ast) : ast_scope.
Notation "'Type<' n >" := (a_typ n) (in custom ast at level 0, n constr at level 0) : ast_scope.
Notation "'Π' T -> S" := (a_pi T S) (in custom ast at level 99, T custom ast at level 0, S custom ast at level 0) : ast_scope.
Number Notation exp num_to_exp exp_to_num : ast_scope.
Notation "0" := a_zero (in custom ast) : ast_scope.
Notation "1" := (a_succ a_zero) (in custom ast) : ast_scope.
Notation "2" := (a_succ (a_succ a_zero)) (in custom ast) : ast_scope.
Notation "'S' e" := (a_succ e) (in custom ast at level 20, e custom ast at level 10) : ast_scope.
Notation "'#' n" := (a_var n) (in custom ast at level 70, n constr at level 0) : ast_scope.
Notation "!" := a_id (in custom ast at level 0) : ast_scope.

Open Scope ast_scope.
Example example := {{ (λ Type<0> -> S S # 0 Type<0>) Type<0> ℕ }}.
Set Printing All.
Print example.

Notation Ctx := (list exp).
Notation Sb := subst.
Notation Typ := exp.
Notation typ := a_typ.
Notation ℕ := a_nat.
Notation 𝝺 := a_fn.
Notation Π := a_pi.
