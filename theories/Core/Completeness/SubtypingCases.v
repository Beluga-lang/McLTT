From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.FunctionCases Evaluation.
Import Domain_Notations.

Lemma sub_typ_subtyp_refl : forall Γ M M' i,
    {{ Γ ⊨ M ≈ M' : Type@i }} ->
    {{ Γ ⊨ M ⊆ M' }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_sub_typ.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  do 2 eexists.
  repeat split; econstructor; mauto 3;
    etransitivity; try eassumption; symmetry; eassumption.
Qed.

Lemma sub_typ_subtyp_trans : forall Γ M M' M'',
    {{ Γ ⊨ M ⊆ M' }} ->
    {{ Γ ⊨ M' ⊆ M'' }} ->
    {{ Γ ⊨ M ⊆ M'' }}.
Proof.
  intros * [env_relΓ [? [i]]] [? [? [j]]].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_sub_typ_with (max i j).
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  do 2 eexists.
  repeat split; econstructor;
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
  etransitivity;
    eauto using per_subtyp_cumu_left, per_subtyp_cumu_right.
Qed.

#[export]
Instance sub_typ_trans Γ : Transitive (sub_typ_under_ctx Γ).
Proof. eauto using sub_typ_subtyp_trans. Qed.

Lemma sub_typ_subtyp_univ : forall Γ i j,
    {{ ⊨ Γ }} ->
    i < j ->
    {{ Γ ⊨ Type@i ⊆ Type@j }}.
Proof.
  intros * [env_relΓ] ?.
  eexists_sub_typ.
  intros.
  assert (i < S (max i j)) by lia.
  assert (j < S (max i j)) by lia.
  do 2 eexists.
  repeat split; econstructor;
    try apply per_univ_elem_core_univ'; try reflexivity;
    mauto 3.
  econstructor; lia.
Qed.

Lemma sub_typ_subtyp_pi : forall Γ A A' B B' i,
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A' ⊨ B ⊆ B' }} ->
  {{ Γ ⊨ Π A B ⊆ Π A' B' }}.
Proof.
  intros * [env_relΓ] [env_relΓA' [? [k]]].
  destruct_conjs.
  pose env_relΓ.
  pose env_relΓA'.
  match_by_head (per_ctx_env env_relΓA') invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  eexists_sub_typ.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  rename x0 into head_rel.

  assert (forall c c', head_rel p p' equiv_p_p' c c' -> env_relΓA' d{{{ p ↦ c }}} d{{{ p' ↦ c' }}}) as HΓA'
      by (intros; apply_relation_equivalence; unshelve eexists; eassumption).

  (* The proofs for the next two assertions are basically the same *)
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Π m0 p B ≈ Π m1 p' B ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [| symmetry]; mauto using per_univ_elem_cumu_max_left.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert (env_relΓA' d{{{ p ↦ c }}} d{{{ p' ↦ c' }}}) as equiv_pc_p'c' by (apply HΓA'; intuition).
      apply_relation_equivalence.
      (on_all_hyp: fun H => destruct (H _ _ equiv_pc_p'c')).
      destruct_conjs.
      destruct_by_head rel_typ.
      econstructor; mauto using per_univ_elem_cumu_max_right.
  }
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Π a0 p B' ≈ Π a p' B' ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [symmetry |]; mauto using per_univ_elem_cumu_max_left.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert (env_relΓA' d{{{ p ↦ c }}} d{{{ p' ↦ c' }}}) as equiv_pc_p'c' by (apply HΓA'; intuition).
      apply_relation_equivalence.
      (on_all_hyp: fun H => destruct (H _ _ equiv_pc_p'c')).
      destruct_conjs.
      destruct_by_head rel_typ.
      econstructor; mauto using per_univ_elem_cumu_max_right.
  }

  do 2 eexists.
  repeat split; econstructor; mauto 2.
  econstructor; only 3-4: try (saturate_refl; mautosolve 2).
  - eauto using per_univ_elem_cumu_max_left.
  - intros.
    assert (env_relΓA' d{{{ p ↦ c }}} d{{{ p' ↦ c' }}}) as equiv_pc_p'c' by (apply HΓA'; intuition).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ equiv_pc_p'c')).
    destruct_conjs.
    destruct_by_head rel_exp.
    simplify_evals.
    mauto 2 using per_subtyp_cumu_right.
Qed.

#[export]
Hint Resolve sub_typ_subtyp_refl sub_typ_subtyp_trans sub_typ_subtyp_univ sub_typ_subtyp_pi : mcltt.
