Require Import String.
Require Import List.

(* CST term *)
Module Cst.
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
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
| a_natrec : exp -> exp -> exp -> exp -> exp
(* Type constructors *)
| a_nat : exp
| a_typ : nat -> exp
| a_var : nat -> exp
(* Functions *)
| a_fn : exp -> exp -> exp
| a_app : exp -> exp -> exp
| a_pi : exp -> exp -> exp
(* Substitutions *)
| a_sub : exp -> sub -> exp
with sub : Set :=
| a_id : sub
| a_weaken : sub
| a_compose : sub -> sub -> sub
| a_extend : sub -> exp -> sub.

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

#[global] Declare Custom Entry exp.
#[global] Declare Scope exp_scope.
#[global] Delimit Scope exp_scope with exp.
#[global] Bind Scope exp_scope with exp.
#[global] Bind Scope exp_scope with sub.
#[global] Bind Scope exp_scope with Sortclass.
Open Scope exp_scope.
Open Scope nat_scope.

Notation "{{{ x }}}" := x (at level 0, x custom exp at level 99, format "'{{{'  x  '}}}'") : exp_scope.
Notation "( x )" := x (in custom exp at level 0, x custom exp at level 60) : exp_scope.
Notation "~ x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "e [ s ]" := (a_sub e s) (in custom exp at level 0, s custom exp at level 60) : exp_scope.
Notation "'λ' T e" := (a_fn T e) (in custom exp at level 0, T custom exp at level 0, e custom exp at level 60) : exp_scope.
Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : exp_scope.
Notation "'ℕ'" := a_nat (in custom exp) : exp_scope.
Notation "'Type' @ n" := (a_typ n) (in custom exp at level 0, n constr at level 0) : exp_scope.
Notation "'Π' T S" := (a_pi T S) (in custom exp at level 0, T custom exp at level 0, S custom exp at level 60) : exp_scope.
Number Notation exp num_to_exp exp_to_num : exp_scope.
Notation "'zero'" := a_zero (in custom exp at level 0) : exp_scope.
Notation "'succ' e" := (a_succ e) (in custom exp at level 0, e custom exp at level 0) : exp_scope.
Notation "'rec' e 'return' m | 'zero' -> ez | 'succ' -> es 'end'" := (a_natrec m ez es e) (in custom exp at level 0, m custom exp at level 60, ez custom exp at level 60, es custom exp at level 60, e custom exp at level 60) : exp_scope.
Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0) : exp_scope.
Notation "'Id'" := a_id (in custom exp at level 0) : exp_scope.
Notation "'Wk'" := a_weaken (in custom exp at level 0) : exp_scope.

Notation "⋅" := nil (in custom exp at level 0) : exp_scope.
Notation "x , y" := (cons y x) (in custom exp at level 50) : exp_scope.

Infix "∘" := a_compose (in custom exp at level 40) : exp_scope.
Infix ",," := a_extend (in custom exp at level 50) : exp_scope.
Notation "'q' σ" := ({{{ σ ∘ Wk ,, # 0 }}}) (in custom exp at level 30) : exp_scope.

Notation ctx := (list exp).
Notation typ := exp.
