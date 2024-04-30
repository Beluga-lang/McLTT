From Mcltt Require Import Syntax.

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

#[global] Declare Custom Entry domain.
#[global] Bind Scope exp_scope with domain.

Notation "'d{{{' x '}}}'" := x (at level 0, x custom domain at level 99, format "'d{{{'  x  '}}}'") : exp_scope.
Notation "( x )" := x (in custom domain at level 0, x custom domain at level 60) : exp_scope.
Notation "~ x" := x (in custom domain at level 0, x constr at level 0) : exp_scope.
Notation "x" := x (in custom domain at level 0, x global) : exp_scope.
Notation "'λ' p M" := (d_fn p M) (in custom domain at level 0, p custom domain at level 30, M custom exp at level 30) : exp_scope.
Notation "f x .. y" := (d_app .. (d_app f x) .. y) (in custom domain at level 40, f custom domain, x custom domain at next level, y custom domain at next level) : exp_scope.
Notation "'ℕ'" := d_nat (in custom domain) : exp_scope.
Notation "'𝕌' @ n" := (d_univ n) (in custom domain at level 0, n constr at level 0) : exp_scope.
Notation "'Π' a p B" := (d_pi a p B) (in custom domain at level 0, a custom domain at level 30, p custom domain at level 0, B custom exp at level 30) : exp_scope.
Notation "'zero'" := d_zero (in custom domain at level 0) : exp_scope.
Notation "'succ' m" := (d_succ m) (in custom domain at level 30, m custom domain at level 30) : exp_scope.
Notation "'rec' m 'under' p 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec p P mz MS m) (in custom domain at level 0, P custom exp at level 60, mz custom domain at level 60, MS custom exp at level 60, p custom domain at level 60, m custom domain at level 60) : exp_scope.
Notation "'!' n" := (d_var n) (in custom domain at level 0, n constr at level 0) : exp_scope.
Notation "'⇑' a m" := (d_neut a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : exp_scope.
Notation "'⇓' a m" := (d_dom a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : exp_scope.
Notation "'⇑!' a n" := (d_neut a (d_var n)) (in custom domain at level 0, a custom domain at level 30, n constr at level 0) : exp_scope.

Definition empty_env : env := fun x => d{{{ zero }}}.
Definition extend_env (p : env) (d : domain) : env :=
  fun n =>
    match n with
    | 0 => d
    | S n' => p n'
    end.
Notation "p ↦ m" := (extend_env p m) (in custom domain at level 20, left associativity) : exp_scope.

Definition drop_env (p : env) : env := fun n => p (S n).
Notation "p '↯'" := (drop_env p) (in custom domain at level 10, p custom domain) : exp_scope.
