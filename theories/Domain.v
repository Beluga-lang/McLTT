Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Unicode.Utf8_core.
Require Export Utf8.


Inductive D : Set :=
| d_nat : D
| d_pi : D -> exp -> Env -> D
| d_typ : nat -> D
| d_zero : D
| d_succ : D -> D
| d_lam :  exp -> Env -> D
| d_up : D -> Dn -> D
with Dn : Set :=
| d_l : nat -> Dn
| d_rec : Typ -> D -> exp -> Env -> Dn -> Dn
| d_app : Dn -> Df -> Dn
with Df : Set :=
| d_down : D -> D -> Df
with Env : Set :=
| d_env : (nat -> D) -> Env
.

Definition d_emp : Env := d_env (λ n, d_zero).

Definition d_lookup (p : Env) : nat -> D :=
  match p with d_env f => f end.

Definition d_drop (p : Env) : Env :=
  match p with d_env f => (d_env (λ n, f (n+1))) end.

Definition d_push (p : Env) (d : D) : Env :=
  match p with d_env f =>
                 (d_env (λ n, match n with
                              | 0 => d
                              | S m => (f m)
                              end
                    )
                 )
  end.

Notation "↑" := d_up.
Notation "↓" := d_down.
Notation "p ↦ d" := (d_push p d) (at level 80).

Notation "'l'' A x" := (↑ (A) (d_l x)) (at level 80, A at next level, x at next level).

Notation "[ A ] x $' y" := (↑ A (d_app x y)) (at level 80).
