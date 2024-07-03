From Mcltt Require Import Base.
From Mcltt.Core Require Import System.Definitions NbE.
From Mcltt Require Export Syntax.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall M N,
    not_univ_pi M ->
    M = N ->
    {{ ⊢anf M ⊆ N }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π A B ⊆ Π A' B' }}
where "⊢anf M ⊆ N" := (alg_subtyping_nf M N) (in custom judg) : type_scope.


Inductive alg_subtyping : ctx -> typ -> typ -> Prop :=
| alg_subtyp_run : forall Γ M N A B,
    nbe_ty Γ M A ->
    nbe_ty Γ N B ->
    {{ ⊢anf A ⊆ B }} ->
    {{ Γ ⊢a M ⊆ N }}
where "Γ ⊢a M ⊆ N" := (alg_subtyping Γ M N) (in custom judg) : type_scope.

#[export]
  Hint Constructors alg_subtyping_nf alg_subtyping: mcltt.
