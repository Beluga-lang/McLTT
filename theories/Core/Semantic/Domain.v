From Mcltt Require Export Syntax.
From Equations Require Import Equations.

Reserved Notation "'env'".

Inductive domain : Set :=
| d_nat : domain
| d_pi : domain -> env -> exp -> domain
| d_univ : nat -> domain
| d_zero : domain
| d_succ : domain -> domain
| d_fn : env -> exp -> domain
| d_neut : domain -> domain_ne -> domain
with domain_ne : Set :=
(** Notice that the number x here is not a de Bruijn index but an absolute
    representation of names.  That is, this number does not change relative to the
    binding structure it currently exists in.
 *)
| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_natrec : env -> typ -> domain -> exp -> domain_ne -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf
where "'env'" := (nat -> domain).

Derive NoConfusion for domain domain_ne domain_nf.

Definition empty_env : env := fun x => d_zero.
Arguments empty_env _ /.

Definition extend_env (ρ : env) (d : domain) : env :=
  fun n =>
    match n with
    | 0 => d
    | S n' => ρ n'
    end.
Arguments extend_env _ _ _ /.
Transparent extend_env.

Definition drop_env (ρ : env) : env := fun n => ρ (S n).
Arguments drop_env _ _ /.
Transparent drop_env.

#[global] Declare Custom Entry domain.
#[global] Bind Scope mcltt_scope with domain.

Module Domain_Notations.
  Export Syntax_Notations.

  Notation "'d{{{' x '}}}'" := x (at level 0, x custom domain at level 99, format "'d{{{'  x  '}}}'") : mcltt_scope.
  Notation "( x )" := x (in custom domain at level 0, x custom domain at level 60) : mcltt_scope.
  Notation "~ x" := x (in custom domain at level 0, x constr at level 0) : mcltt_scope.
  Notation "x" := x (in custom domain at level 0, x ident) : mcltt_scope.
  Notation "'λ' ρ M" := (d_fn ρ M) (in custom domain at level 0, ρ custom domain at level 30, M custom exp at level 30) : mcltt_scope.
  Notation "f x .. y" := (d_app .. (d_app f x) .. y) (in custom domain at level 40, f custom domain, x custom domain at next level, y custom domain at next level) : mcltt_scope.
  Notation "'ℕ'" := d_nat (in custom domain) : mcltt_scope.
  Notation "'𝕌' @ n" := (d_univ n) (in custom domain at level 0, n constr at level 0) : mcltt_scope.
  Notation "'Π' a ρ B" := (d_pi a ρ B) (in custom domain at level 0, a custom domain at level 30, ρ custom domain at level 0, B custom exp at level 30) : mcltt_scope.
  Notation "'zero'" := d_zero (in custom domain at level 0) : mcltt_scope.
  Notation "'succ' m" := (d_succ m) (in custom domain at level 30, m custom domain at level 30) : mcltt_scope.
  Notation "'rec' m 'under' ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ P mz MS m) (in custom domain at level 0, P custom exp at level 60, mz custom domain at level 60, MS custom exp at level 60, ρ custom domain at level 60, m custom domain at level 60) : mcltt_scope.
  Notation "'!' n" := (d_var n) (in custom domain at level 0, n constr at level 0) : mcltt_scope.
  Notation "'⇑' a m" := (d_neut a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mcltt_scope.
  Notation "'⇓' a m" := (d_dom a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mcltt_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (in custom domain at level 0, a custom domain at level 30, n constr at level 0) : mcltt_scope.

  Notation "ρ ↦ m" := (extend_env ρ m) (in custom domain at level 20, left associativity) : mcltt_scope.
  Notation "ρ '↯'" := (drop_env ρ) (in custom domain at level 10, ρ custom domain) : mcltt_scope.
End Domain_Notations.

Import Domain_Notations.

Proposition drop_env_extend_env_cancel : forall ρ a,
    d{{{ (ρ ↦ a) ↯ }}} = ρ.
Proof.
  reflexivity.
Qed.
