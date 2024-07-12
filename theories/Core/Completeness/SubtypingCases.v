From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.FunctionCases Evaluation.
Import Domain_Notations.


Lemma sub_typ_subtyp_refl : forall Γ M M' i,
    {{ Γ ⊨ M ≈ M' : Type@i }} ->
    {{ Γ ⊨ M ⊆ M' }}.
Proof.
  intros * [R [HR [i H]]].
  do 3 try eexists; eauto.
  intros.
  saturate_refl.
  destruct (H _ _ equiv_p_p') as [elem_relpp' [[] []]].
  destruct (H _ _ H0) as [elem_relpp [[] []]].
  destruct (H _ _ H1) as [elem_relp'p' [[] []]].
  repeat match goal with
         | H : eval_exp _ _ _ |- _ => progressive_invert H
         end.
  simplify_evals.
  on_all_hyp: fun H => directed invert_per_univ_elem H.
  apply_equiv_left.
  destruct_all.
  handle_per_univ_elem_irrel.
  do 2 eexists. repeat split.
  - econstructor; eauto.
    etransitivity; [eassumption |].
    symmetry. eassumption.
  - econstructor; eauto.
    etransitivity; [symmetry; eassumption |].
    eassumption.
  - econstructor; eauto.
    eauto using per_subtyp_refl1.
Qed.


Lemma sub_typ_subtyp_trans : forall Γ M M' M'',
    {{ Γ ⊨ M ⊆ M' }} ->
    {{ Γ ⊨ M' ⊆ M'' }} ->
    {{ Γ ⊨ M ⊆ M'' }}.
Proof.
  intros * [R [HR [i H]]] [R' [HR' [j H']]].
  handle_per_ctx_env_irrel.
  do 2 try eexists; eauto.
  exists (max i j).
  intros.
  saturate_refl_for R'.
  on_all_hyp: fun H1 =>
                lazymatch type of H1 with
                | R' ?a ?b =>
                    let H2 := fresh "H" in
                    assert (R a b) as H2 by firstorder;
                    destruct (H' _ _ H1) as [? [? [[] [[] []]]]];
                    destruct (H _ _ H2) as [? [? [[] [[] []]]]]
                end.
  simplify_evals.
  handle_per_univ_elem_irrel.
  do 2 eexists. repeat split.
  - econstructor; eauto.
    eauto using per_univ_elem_cumu_max_left.
  - econstructor; eauto.
    eauto using per_univ_elem_cumu_max_right.
  - econstructor; eauto.
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
  intros * [R HR] ?.
  do 2 try eexists; eauto.
  exists (S (max i j)).
  intros.
  do 2 eexists; repeat split;
  econstructor; mauto 2.
  - apply per_univ_elem_core_univ'; [lia | reflexivity].
  - apply per_univ_elem_core_univ'; [lia | reflexivity].
  - econstructor; lia.
Qed.


Lemma sub_typ_subtyp_pi : forall Γ A A' B B' i,
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A' ⊨ B ⊆ B' }} ->
  {{ Γ ⊨ Π A B ⊆ Π A' B' }}.
Proof.
  intros * [RAA' [HRAA' [j HAA']]]
             [RBB' [HRBB' [k HBB']]].
  progressive_invert HRBB'.
  handle_per_ctx_env_irrel.
  do 2 try eexists; eauto.
  exists (max i k).
  intros.
  saturate_refl_for tail_rel.
  on_all_hyp: fun H1 =>
                lazymatch type of H1 with
                | tail_rel ?a ?b =>
                    let H2 := fresh "H" in
                    assert (RAA' a b) as H2 by firstorder;
                    destruct (HAA' _ _ H2) as [? [[] []]]
                end.
  match_by_head eval_exp progressive_invert.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  clear_eqs. clear_dups. apply_equiv_left.
  destruct_all.
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert (forall c c', H25 c c' -> env_rel d{{{ p ↦ c }}} d{{{ p0 ↦ c' }}}).
  {
    intros. apply_equiv_left.
    unshelve eexists; [eassumption |].
    edestruct (H0 d{{{ (p ↦ c) ↯ }}} d{{{ (p0 ↦ c') ↯ }}}) as [].
    simplify_evals.
    handle_per_univ_elem_irrel.
    apply_equiv_left.
    eassumption.
  }

  assert (per_univ (Nat.max i k) d{{{ Π m0 p B }}} d{{{ Π m p0 B }}}).
  {
    eexists. eapply per_univ_elem_pi'; [ | | solve_refl].
    - apply per_univ_elem_cumu_max_left.
      etransitivity; [| symmetry; eassumption].
      eassumption.
    - apply rel_exp_pi_core; [|reflexivity].
      intros.
      destruct (HBB' d{{{ p ↦ c }}} d{{{ p0 ↦ c' }}}) as [R [R' [[] []]]];
        [firstorder |].
      econstructor; eauto.
      eexists. mauto using per_univ_elem_cumu_max_right.
  }

  assert (per_univ (Nat.max i k) d{{{ Π m'0 p B' }}} d{{{ Π m' p0 B' }}}).
  {
    eexists. eapply per_univ_elem_pi'; [ | | solve_refl].
    - apply per_univ_elem_cumu_max_left.
      etransitivity; [symmetry; eassumption |].
      eassumption.
    - apply rel_exp_pi_core; [|reflexivity].
      intros.
      destruct (HBB' d{{{ p ↦ c }}} d{{{ p0 ↦ c' }}}) as [R [R' [? [[] ?]]]];
        [firstorder |].
      econstructor; eauto.
      eexists. mauto using per_univ_elem_cumu_max_right.
  }

  match_by_head per_univ ltac:(fun H => destruct H as []).
  do 2 eexists. repeat split; econstructor; mauto 2.

  saturate_refl.
  econstructor; try eassumption.
  - eauto using per_univ_elem_cumu_max_left.
  - intros.
    destruct (HBB' d{{{ p ↦ c }}} d{{{ p0 ↦ c' }}}) as [R [R' [? [? []]]]];
      [firstorder |].
    simplify_evals.
    mauto 2 using per_subtyp_cumu_right.
Qed.

#[export]
 Hint Resolve sub_typ_subtyp_refl sub_typ_subtyp_trans sub_typ_subtyp_univ sub_typ_subtyp_pi : mcltt.
