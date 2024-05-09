From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics LogicalRelation System.
Import Domain_Notations.

Lemma rel_exp_sub_cong : forall {Δ M M' A σ σ' Γ},
    {{ Δ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ] }}.
Proof.
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  per_ctx_env_irrel_rewrite.
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  assert (env_relΓ p p) by (eapply per_env_trans; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  per_univ_elem_irrel_rewrite.
  assert (env_relΔ o o0) by (eapply per_env_trans; [eauto | | eapply per_env_sym]; revgoals; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΔ H).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  per_univ_elem_irrel_rewrite.
  eexists.
  split; [> econstructor; only 1-2: econstructor; eauto ..].
Qed.

Lemma rel_exp_conv : forall {Γ M M' A A' i},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof.
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  per_ctx_env_irrel_rewrite.
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  assert (env_relΓ p p) by (eapply per_env_trans; eauto; eapply per_env_sym; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  per_univ_elem_irrel_rewrite.
  match_by_head1 per_univ_elem ltac:(fun H => invert_per_univ_elem H; let n := numgoals in guard n <= 1); clear_refl_eqs.
  destruct_conjs.
  per_univ_elem_irrel_rewrite.
  eexists.
  split; [> econstructor; eauto ..].
  eapply per_univ_trans; [eapply per_univ_sym |]; eauto.
Qed.

Lemma rel_exp_sym : forall {Γ M M' A},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' ≈ M : A }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  econstructor.
  eexists; try eassumption.
  eexists.
  intros ? ? equiv_p_p'.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H); destruct_conjs.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  per_univ_elem_irrel_rewrite.
  eexists.
  split; econstructor; eauto.
  eapply per_elem_sym; eauto.
Qed.

Lemma rel_exp_trans : forall {Γ M1 M2 M3 A},
    {{ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ Γ ⊨ M1 ≈ M3 : A }}.
Proof.
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  per_ctx_env_irrel_rewrite.
  econstructor.
  eexists; try eassumption.
  eexists.
  intros ? ? equiv_p_p'.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  assert (env_relΓ p' p') by (eapply per_env_trans; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H); destruct_conjs.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  per_univ_elem_irrel_rewrite.
  eexists.
  split; econstructor; eauto.
  eapply per_elem_trans; eauto.
Qed.
