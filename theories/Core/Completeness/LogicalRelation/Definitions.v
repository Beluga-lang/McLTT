From Coq Require Import Relations.
From Mcltt Require Import Base.
From Mcltt.Core Require Export Evaluation PER.
Import Domain_Notations.

Inductive rel_exp M p M' p' (R : relation domain) : Prop :=
| mk_rel_exp : forall m m', {{ ⟦ M ⟧ p ↘ m }} -> {{ ⟦ M' ⟧ p' ↘ m' }} -> {{ Dom m ≈ m' ∈ R }} -> rel_exp M p M' p' R.
#[global]
Arguments mk_rel_exp {_ _ _ _ _}.
#[export]
Hint Constructors rel_exp : mcltt.

Definition rel_exp_under_ctx Γ A M M' :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
  forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_rel }}),
  exists (elem_rel : relation domain),
     rel_typ i A p A p' elem_rel /\ rel_exp M p M' p' elem_rel.

Definition valid_exp_under_ctx Γ A M := rel_exp_under_ctx Γ A M M.
#[global]
Arguments valid_exp_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_exp_under_ctx : mcltt.
#[export]
Hint Unfold valid_exp_under_ctx : mcltt.

Inductive rel_sub σ p σ' p' (R : relation env) : Prop :=
| mk_rel_sub : forall o o', {{ ⟦ σ ⟧s p ↘ o }} -> {{ ⟦ σ' ⟧s p' ↘ o' }} -> {{ Dom o ≈ o' ∈ R }} -> rel_sub σ p σ' p' R.
#[global]
Arguments mk_rel_sub {_ _ _ _ _ _}.
#[export]
Hint Constructors rel_sub : mcltt.

Definition rel_sub_under_ctx Γ Δ σ σ' :=
  exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }})
     env_rel' (_ : {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_rel' }}),
  forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_rel }}),
    rel_sub σ p σ' p' env_rel'.

Definition valid_sub_under_ctx Γ Δ σ := rel_sub_under_ctx Γ Δ σ σ.
#[global]
Arguments valid_sub_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_sub_under_ctx : mcltt.
#[export]
Hint Unfold valid_sub_under_ctx : mcltt.

Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Notation "⊨ Γ" := (valid_ctx Γ) (in custom judg at level 80, Γ custom exp).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Notation "Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Notation "Γ ⊨s σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
