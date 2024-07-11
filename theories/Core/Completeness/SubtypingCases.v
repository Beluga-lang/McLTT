From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Evaluation.
Import Domain_Notations.


Lemma wf_subtyp_refl' : forall Γ M M' i,
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


Lemma wf_subtyp_trans' : forall Γ M M' M'',
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

(* | wf_subtyp_univ : *)
(*   `( {{ ⊢ Γ }} -> *)
(*      i < j -> *)
(*      {{ Γ ⊢ Type@i ⊆ Type@j }} ) *)
(* | wf_subtyp_pi : *)
(*   `( {{ Γ ⊢ A : Type@i }} -> *)
(*      {{ Γ ⊢ A' : Type@i }} -> *)
(*      {{ Γ ⊢ A ≈ A' : Type@i }} -> *)
(*      {{ Γ , A ⊢ B : Type@i }} -> *)
(*      {{ Γ , A' ⊢ B' : Type@i }} -> *)
(*      {{ Γ , A' ⊢ B ⊆ B' }} -> *)
(*      {{ Γ ⊢ Π A B ⊆ Π A' B' }} ) *)


#[export]
 Hint Resolve wf_subtyp_refl' wf_subtyp_trans' : mcltt.
