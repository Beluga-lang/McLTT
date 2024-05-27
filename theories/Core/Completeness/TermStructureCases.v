From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation System.
Import Domain_Notations.

Lemma rel_exp_sub_cong : forall {Δ M M' A σ σ' Γ},
    {{ Δ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  pose (env_relΔ0 := env_relΔ).
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eassumption).
  assert (env_relΓ p p) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_univ_elem_irrel.
  assert (env_relΔ o o0) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: econstructor; eassumption ..].
Qed.

#[export]
Hint Resolve rel_exp_sub_cong : mcltt.

Lemma rel_exp_sub_id : forall {Γ M A},
    {{ Γ ⊨ M : A }} ->
    {{ Γ ⊨ M[Id] ≈ M : A }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  eexists.
  split; econstructor; try eassumption.
  repeat econstructor; eassumption.
Qed.

#[export]
Hint Resolve rel_exp_sub_id : mcltt.

Lemma rel_exp_sub_compose : forall {Γ τ Γ' σ Γ'' M A},
    {{ Γ ⊨s τ : Γ' }} ->
    {{ Γ' ⊨s σ : Γ'' }} ->
    {{ Γ'' ⊨ M : A }} ->
    {{ Γ ⊨ M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] [].
  destruct_conjs.
  pose (env_relΓ'0 := env_relΓ').
  pose (env_relΓ''0 := env_relΓ'').
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  assert (env_relΓ p p) by (eapply per_env_trans; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_univ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_univ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eassumption ..].
Qed.

#[export]
Hint Resolve rel_exp_sub_compose : mcltt.

Lemma rel_exp_conv : forall {Γ M M' A A' i},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p p) by (eapply per_env_trans; eauto; eapply per_env_sym; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; try eassumption.
  etransitivity; [symmetry |]; eassumption.
Qed.

#[export]
Hint Resolve rel_exp_conv : mcltt.

Lemma rel_exp_sym : forall {Γ M M' A},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' ≈ M : A }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; try eassumption.
  symmetry; eassumption.
Qed.

#[export]
Hint Resolve rel_exp_sym : mcltt.

Lemma rel_exp_trans : forall {Γ M1 M2 M3 A},
    {{ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ Γ ⊨ M1 ≈ M3 : A }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eauto).
  assert (env_relΓ p' p') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; try eassumption.
  etransitivity; eassumption.
Qed.

#[export]
Hint Resolve rel_exp_trans : mcltt.

#[export]
Instance rel_exp_PER {Γ A} : PER (rel_exp_under_ctx Γ A).
Proof.
  split; mauto.
Qed.

Lemma presup_rel_exp : forall {Γ M M' A},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ ⊨ Γ }} /\ {{ Γ ⊨ M : A }} /\ {{ Γ ⊨ M' : A }} /\ exists i, {{ Γ ⊨ A : Type@i }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros *.
  assert (Hpart : {{ Γ ⊨ M ≈ M' : A }} -> {{ Γ ⊨ M : A }} /\ {{ Γ ⊨ M' : A }}) by
    (split; unfold valid_exp_under_ctx; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head valid_exp_under_ctx.
    destruct_conjs.
    eexists.
    eexists_rel_exp.
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eexists (per_univ _).
    split.
    + econstructor; only 1-2: repeat econstructor; try eassumption.
      per_univ_elem_econstructor; eauto.
      apply Equivalence_Reflexive.
    + eapply rel_typ_implies_rel_exp; eassumption.
Qed.
