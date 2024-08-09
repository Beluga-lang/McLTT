From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation EquivalenceLemmas.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

(* TODO: move this to a better place *)
Lemma destruct_glu_rel_exp : forall {Γ Sb M A},
  {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
  {{ Γ ⊩ M : A }} ->
  exists i,
  forall Δ σ ρ,
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_exp_sub i Δ M A σ ρ.
Proof.
  intros * ? [Sb'].
  destruct_conjs.
  eexists; intros.
  (* TODO: handle functional glu_ctx_env here *)
  assert (Sb <∙> Sb') by admit.
  apply_predicate_equivalence.
  mauto.
Admitted.

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
  econstructor; split; [eassumption |].
  exists (max i j); intros.
  (* TODO: extract this as a tactic *)
  match goal with
  | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ => edestruct H; try eassumption
  end.
  (* TODO: introduce a lemma for glu_ctx_env *)
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by admit.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  rename m' into a'.
  (* assert (exists P' El', {{ DG a' ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }}) as [P' [El']]. *)
  (* { *)
  (*   assert (exists R R', {{ DF a ≈ a ∈ per_univ_elem j ↘ R }} /\ {{ DF a' ≈ a' ∈ per_univ_elem j ↘ R' }}) by mauto using per_subtyp_to_univ_elem. *)
  (*   destruct_conjs. *)
  (*   assert {{ Dom a' ≈ a' ∈ per_univ (max i j) }} by (eexists; mauto using per_univ_elem_cumu_max_right). *)
  (*   apply per_univ_glu_univ_elem; mauto. *)
  (* } *)
  (* econstructor; try eassumption. *)
Admitted.
