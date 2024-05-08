From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Mcltt Require Import Axioms Base Evaluation LibTactics PERDefinitions.
From Mcltt Require Export PERBasicLemmas.
Import Domain_Notations.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    try solve [inversion Hright; congruence].
  subst.
  inversion_clear Hright.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  subst.
  enough (head_rel = head_rel0) by (subst; easy).
  extensionality p.
  extensionality p'.
  extensionality equiv_p_p'.
  unfold rel_typ in *.
  destruct_rel_mod_eval.
  per_univ_elem_irrel_rewrite.
  congruence.
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }} /\ (forall o p, {{ Dom o ≈ p ∈ R }} -> {{ Dom p ≈ o ∈ R }}).
Proof with solve [eauto].
  simpl.
  induction 1; firstorder; try solve [econstructor; eauto]; unfold rel_typ in *.
  - econstructor; eauto; firstorder.
    assert (tail_rel p' p) by eauto.
    assert (tail_rel p p) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite.
    econstructor; eauto.
    apply per_univ_elem_sym...
  - subst.
    firstorder.
    assert (tail_rel d{{{ p ↯ }}} d{{{ o ↯ }}}) by (unfold Symmetric in *; eauto).
    assert (tail_rel d{{{ p ↯ }}} d{{{ p ↯ }}}) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    eexists.
    per_univ_elem_irrel_rewrite.
    eapply per_univ_elem_sym...
Qed.

Lemma per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * []%per_ctx_env_sym []%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Lemma per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * ? []%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_rewrite1 :=
  match goal with
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_ctx_env_right_irrel)
    | H1 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_ctx_env_left_irrel)
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (* Order matters less here as H1 and H2 cannot be exchanged *)
        clean replace R2 with R1 by (symmetry; eauto using per_ctx_env_cross_irrel)
    end.

Ltac do_per_ctx_env_irrel_rewrite :=
  repeat do_per_ctx_env_irrel_rewrite1.

Ltac per_ctx_env_irrel_rewrite :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_rewrite;
  clear_dups.

Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    forall Γ3,
      {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R }} ->
      {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R }} /\ (forall p1 p2 p3, {{ Dom p1 ≈ p2 ∈ R }} -> {{ Dom p2 ≈ p3 ∈ R }} -> {{ Dom p1 ≈ p3 ∈ R }}).
Proof with solve [eauto].
  simpl.
  induction 1; intros * HTrans23; inversion HTrans23; subst; eauto.
  per_ctx_env_irrel_rewrite.
  rename tail_rel0 into tail_rel.
  split.
  - econstructor; eauto.
    + eapply IHper_ctx_env...
    + unfold rel_typ in *.
      intros.
      assert (tail_rel p p) by (etransitivity; [ | symmetry]; eassumption).
      destruct_rel_mod_eval.
      econstructor; eauto.
      per_univ_elem_irrel_rewrite.
      eapply proj1, per_univ_elem_trans; [|eassumption]...
  - intros * [] [].
    specialize (IHper_ctx_env _ equiv_Γ_Γ'0) as [].
    assert (tail_rel d{{{ p1 ↯ }}} d{{{ p3 ↯ }}}) by eauto.
    eexists.
    unfold rel_typ in *.
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite.
    eapply per_univ_elem_trans...
Qed.
