From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Syntactic Require Import Corollaries.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Lemma glu_univ_elem_typ_escape : forall {i j a P P' El El' Γ A A'},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max i j) }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A ® glu_typ_top i a }} as [] by mauto 3.
  assert {{ Γ ⊢ A' ® glu_typ_top j a }} as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert {{ Γ ⊢ A : Type@(max i j) }} by mauto 4 using lift_exp_max_left.
  assert {{ Γ ⊢ A' : Type@(max i j) }} by mauto 4 using lift_exp_max_right.
  assert {{ Γ ⊢ A[Id] ≈ V : Type@i }} by mauto 4.
  assert {{ Γ ⊢ A[Id] ≈ V : Type@(max i j) }} by mauto 4 using lift_exp_eq_max_left.
  assert {{ Γ ⊢ A'[Id] ≈ V : Type@j }} by mauto 4.
  assert {{ Γ ⊢ A'[Id] ≈ V : Type@(max i j) }} by mauto 4 using lift_exp_eq_max_right.
  autorewrite with mcltt in *...
Qed.

#[export]
Hint Resolve glu_univ_elem_typ_escape : mcltt.

Lemma glu_univ_elem_typ_escape_ge : forall {i j a P P' El El' Γ A A'},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof with mautosolve 4.
  intros.
  replace j with (max i j) by lia...
Qed.

#[export]
Hint Resolve glu_univ_elem_typ_escape_ge : mcltt.

Lemma glu_univ_elem_typ_escape' : forall {i a P El Γ A A'},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_univ_elem_typ_escape' : mcltt.

Lemma glu_univ_elem_per_univ_elem_typ_escape : forall {i a a' elem_rel P P' El El' Γ A A'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof with mautosolve 4.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} by (setoid_rewrite Hper; eassumption).
  handle_functional_glu_univ_elem...
Qed.

#[export]
Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mcltt.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof.
  intros * [] **...
  mauto 4.
Qed.

Lemma glu_univ_elem_per_univ_typ_iff : forall {i a a' P P' El El'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  intros * Hper **.
  eapply functional_glu_univ_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.
