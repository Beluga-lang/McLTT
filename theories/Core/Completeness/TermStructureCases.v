From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics LogicalRelation System.
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
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  assert (env_relΓ p' p) by (symmetry; eauto).
  assert (env_relΓ p p) by (etransitivity; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  handle_per_univ_elem_irrel.
  assert (env_relΔ o o0) by (etransitivity; [|symmetry; intuition]; intuition).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΔ H).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: econstructor; eauto ..].
Qed.

Lemma rel_exp_sub_id : forall {Γ M A},
    {{ Γ ⊨ M : A }} ->
    {{ Γ ⊨ M[Id] ≈ M : A }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  eexists.
  split; econstructor; eauto.
  repeat econstructor; mauto.
Qed.

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
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  assert (env_relΓ p' p) by (eapply per_env_sym; eauto).
  assert (env_relΓ p p) by (eapply per_env_trans; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ' H).
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ'' H).
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
Qed.

Lemma rel_exp_conv : forall {Γ M M' A A' i},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A' }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  eexists.
  eexists; try eassumption.
  eexists.
  intros.
  assert (env_relΓ p p) by (eapply per_env_trans; eauto; eapply per_env_sym; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  handle_per_univ_elem_irrel.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; eauto.
  etransitivity; [symmetry |]; eauto.
Qed.

Lemma rel_exp_sym : forall {Γ M M' A},
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ M' ≈ M : A }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
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
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; eauto.
  eapply per_elem_sym; eauto.
Qed.

Lemma rel_exp_trans : forall {Γ M1 M2 M3 A},
    {{ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ Γ ⊨ M1 ≈ M3 : A }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  econstructor.
  eexists; try eassumption.
  eexists.
  intros ? ? equiv_p_p'.
  assert (env_relΓ p' p) by (symmetry; eauto).
  assert (env_relΓ p' p') by (etransitivity; eauto).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H); destruct_conjs.
  destruct_by_head rel_exp.
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; eauto.
  etransitivity; eauto.
Qed.
