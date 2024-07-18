From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation Completeness.LogicalRelation Completeness.UniverseCases.
Import Domain_Notations.

Lemma rel_exp_sub_cong : forall {Δ M M' A σ σ' Γ},
    {{ Δ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ] }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eassumption).
  assert (env_relΓ p p) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_univ_elem_irrel.
  assert (env_relΔ o o0) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_cong : mcltt.

Lemma rel_exp_sub_id : forall {Γ M A},
    {{ Γ ⊨ M : A }} ->
    {{ Γ ⊨ M[Id] ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_id : mcltt.

Lemma rel_exp_sub_compose : forall {Γ τ Γ' σ Γ'' M A},
    {{ Γ ⊨s τ : Γ' }} ->
    {{ Γ' ⊨s σ : Γ'' }} ->
    {{ Γ'' ⊨ M : A }} ->
    {{ Γ ⊨ M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] [].
  destruct_conjs.
  pose env_relΓ'.
  pose env_relΓ''.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eassumption).
  assert (env_relΓ p p) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_univ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_univ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_sub_compose : mcltt.

Lemma rel_exp_conv : forall {Γ M M' A A' i},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] []%rel_exp_of_typ_inversion.
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p p) by (etransitivity; [| symmetry]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; mauto.
  etransitivity; [symmetry |]...
Qed.

#[export]
Hint Resolve rel_exp_conv : mcltt.

Lemma rel_exp_sym : forall {Γ M M' A},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' ≈ M : A }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; mauto.
  symmetry...
Qed.

#[export]
Hint Resolve rel_exp_sym : mcltt.

Lemma rel_exp_trans : forall {Γ M1 M2 M3 A},
    {{ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ Γ ⊨ M1 ≈ M3 : A }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ p' p) by (symmetry; eauto).
  assert (env_relΓ p' p') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; mauto.
  etransitivity...
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
  assert (Hpart : {{ Γ ⊨ M ≈ M' : A }} -> {{ Γ ⊨ M : A }} /\ {{ Γ ⊨ M' : A }})
    by (split; unfold valid_exp_under_ctx; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head valid_exp_under_ctx.
    destruct_conjs.
    eexists.
    eexists_rel_exp_of_typ.
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eapply rel_typ_implies_rel_exp; eauto.
Qed.


Lemma rel_exp_eq_subtyp : forall Γ M M' A A',
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A ⊆ A' }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [i]]] [? [? [j]]].
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_with (max i j).
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  simplify_evals.
  eexists.
  split; econstructor; eauto using per_univ_elem_cumu_max_right.
  handle_per_univ_elem_irrel.
  eapply per_elem_subtyping_gen with (i := max i j); try eassumption.
  - eauto using per_subtyp_cumu_right.
  - eauto using per_univ_elem_cumu_max_right.
  - symmetry. eauto using per_univ_elem_cumu_max_right.
Qed.

#[export]
Hint Resolve rel_exp_eq_subtyp : mcltt.
