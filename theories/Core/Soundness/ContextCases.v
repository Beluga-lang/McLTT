From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses SetoidTactics.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_ctx_empty : {{ ⊩ ⋅ }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcltt.

Lemma glu_rel_ctx_extend : forall {Γ A i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ ⊩ Γ , A }}.
Proof.
  intros * [Sb] HA.
  destruct (invert_glu_rel_exp ltac:(eassumption) HA) as [].
  eexists.
  econstructor; mauto; try reflexivity.
  intros.
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
  handle_functional_glu_ctx_env.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcltt.
