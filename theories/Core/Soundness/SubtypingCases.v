From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_subtyp : forall {Γ M A A' i},
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ A' : Type@i }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊩ M : A' }}.
Proof.
  intros * [Sb [? [i]]] HA' [env_relΓ [? [j]]]%completeness_fundamental_subtyp.
  destruct_conjs.
  invert_glu_rel_exp HA'.
  destruct_conjs.
  rename i0 into k.
  econstructor; split; [eassumption |].
  exists (max i (max j k)); intros.
  destruct_glu_rel_exp_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  rename m into a'.
  rename a0 into a.
  rename m0 into m.
  rename P0 into P.
  rename El0 into El.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; mauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  eapply mk_glu_rel_exp_sub''; gintuition mauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
  eapply glu_univ_elem_per_subtyp_trm_conv; mauto.
  assert (k <= max i (max j k)) by lia.
  eapply glu_univ_elem_typ_cumu_ge; revgoals; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_subtyp : mcltt.

Lemma glu_rel_sub_subtyp : forall {Γ σ Δ Δ'},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Δ' }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊩s σ : Δ' }}.
Proof.
  intros * [SbΓ [SbΔ]] [SbΔ'] Hsubtyp.
  destruct_conjs.
  econstructor; eexists; repeat split; [eassumption | eassumption |].
  intros.
  destruct_glu_rel_sub_sub.
  econstructor; mauto.
  eapply glu_ctx_env_subtyp_sub_if; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_subtyp : mcltt.
