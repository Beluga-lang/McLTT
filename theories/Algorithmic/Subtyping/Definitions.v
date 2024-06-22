From Mcltt Require Import Base.
From Mcltt.Core Require Import System.Definitions NbE.
From Mcltt Require Export Syntax.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Γ ⊢anf A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom nf, A' custom nf).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : ctx -> nf -> nf -> Prop :=
| asnf_refl : forall Γ M N,
    not_univ_pi M ->
    M = N ->
    {{ Γ ⊢anf M ⊆ N }}
| asnf_univ : forall Γ i j,
    i <= j ->
    {{ Γ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall Γ A B A' B',
    {{ Γ ⊢anf A' ⊆ A }} ->
    {{ Γ , ~(nf_to_exp A') ⊢anf B ⊆ B' }} ->
    {{ Γ ⊢anf Π A B ⊆ Π A' B' }}
where "Γ ⊢anf M ⊆ N" := (alg_subtyping_nf Γ M N) (in custom judg) : type_scope.


Inductive alg_subtyping : ctx -> typ -> typ -> Prop :=
| alg_subtyp_run :
  forall Γ M N i j A B,
    nbe Γ M {{{ Type@i }}} A ->
    nbe Γ N {{{ Type@j }}} B ->
    {{ Γ ⊢anf A ⊆ B }} ->
    {{ Γ ⊢a M ⊆ N }}
where "Γ ⊢a M ⊆ N" := (alg_subtyping Γ M N) (in custom judg) : type_scope.

#[export]
  Hint Constructors alg_subtyping_nf alg_subtyping: mcltt.
