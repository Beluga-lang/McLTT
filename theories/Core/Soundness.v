From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Semantic Require Export NbE.
From Mcltt.Core.Soundness Require Import FundamentalTheorem Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Theorem soundness : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * H.
  assert {{ ⊢ Γ }} by mauto.
  assert {{ ⊨ Γ }} as [env_relΓ] by (apply completeness_fundamental_ctx; eassumption).
  destruct (soundness_fundamental_exp _ _ _ H) as [Sb [? [i]]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [p].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® p ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto).
  destruct_glu_rel_exp_with_sub.
  assert {{ Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top; mauto).
  match_by_head per_top ltac:(fun H => destruct (H (length Γ)) as [W []]).
  eexists.
  split; [econstructor |]; try eassumption.
  assert {{ Γ ⊢ A : Type@i }} by mauto 4 using glu_univ_elem_univ_lvl.
  assert {{ Γ ⊢ A[Id] ≈ A : Type@i }} by mauto.
  assert {{ Γ ⊢ A[Id][Id] ≈ A : Type@i }} as <- by mauto 4.
  assert {{ Γ ⊢ M ≈ M[Id] : A[Id][Id] }} by mauto.
  assert {{ Γ ⊢ M ≈ M[Id][Id] : A[Id][Id] }} as -> by mauto.
  mauto.
Qed.

Theorem soundness' : forall {Γ M A W},
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A W ->
    {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * [? []]%soundness ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Lemma soundness_ty : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Proof.
  intros.
  assert (exists W', nbe Γ A {{{ Type@i }}} W' /\ {{ Γ ⊢ A ≈ W' : Type@i }}) as [? [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
  firstorder.
Qed.

Lemma soundness_ty' : forall {Γ i A B},
    {{ Γ ⊢ A : Type@i }} ->
    nbe_ty Γ A B ->
    {{ Γ ⊢ A ≈ B : Type@i }}.
Proof.
  intros.
  assert (exists B', nbe_ty Γ A B' /\ {{ Γ ⊢ A ≈ B' : Type@i }}) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
