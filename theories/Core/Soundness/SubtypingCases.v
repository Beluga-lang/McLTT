From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_subtyp : forall {Γ M A A' i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ A' : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊩ M : A' }}.
Proof.
  intros * HA HA' [Sb [? [i]]] [env_relΓ [? [j]]]%completeness_fundamental_subtyp.
  destruct_conjs.
  eapply destruct_glu_rel_exp in HA, HA'; try eassumption.
  destruct_conjs.
  rename i0 into k.
  econstructor; split; [eassumption |].
  exists (max i (max j k)); intros.
  (* TODO: extract this as a tactic *)
  repeat match goal with
         | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; try eassumption; mark H
             end
         end; unmark_all.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  simpl in *.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; mauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  assert (exists P El, glu_univ_elem (max i (max j k)) P El m0) as [? []].
  {
    assert (exists P El, glu_univ_elem (max j k) P El m0) as [? []];
      mauto using glu_univ_elem_cumu_max_right.
  }
  econstructor; try eassumption.
  assert {{ Sub m <: m0 at max i (max j k) }} by mauto using per_subtyp_cumu_left, per_subtyp_cumu_right.
  assert (exists P El, glu_univ_elem (max i (max j k)) P El m) as [? []] by mauto using glu_univ_elem_cumu_max_left.
  eapply glu_univ_elem_per_subtyp_trm_if; mauto.
  - assert (k <= max i (max j k)) by lia.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mauto.
  - assert (i <= max i (max j k)) by lia.
    eapply glu_univ_elem_exp_cumu_ge; mauto.
Qed.

Lemma glu_rel_sub_subtyp : forall {Γ σ Δ Δ'},
    {{ ⊩ Δ' }} ->
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊩s σ : Δ' }}.
Proof.
  intros * [SbΔ'] [SbΓ [SbΔ]] Hsubtyp.
  pose proof (completeness_fundamental_ctx_sub _ _ Hsubtyp).
  destruct_conjs.
  econstructor; eexists; repeat split; [eassumption | eassumption |].
  intros.
  (* TODO: extract this as a tactic *)
  repeat match goal with
         | H: context[glu_rel_sub_sub _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; try eassumption; mark H
             end
         end; unmark_all.
  econstructor; mauto.
  eapply glu_ctx_env_per_ctx_subtyp_sub_if; only 3: eassumption; mauto.
Qed.
