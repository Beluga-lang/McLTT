From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Completeness.FundamentalTheorem Completeness.LogicalRelation Semantic.Realizability PER.
From Mcltt.Core Require Export SystemOpt.
Import Domain_Notations.

Lemma ctxeq_nbe_eq : forall Γ Γ' M A,
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    exists w, nbe Γ M A w /\ nbe Γ' M A w.
Proof.
  intros ? ? ? ? [envR [Henv [i ?]]]%completeness_fundamental_exp [envR' Henv']%completeness_fundamental_ctx_eq.
  handle_per_ctx_env_irrel.
  destruct (per_ctx_then_per_env_initial_env Henv') as [p [p' [? [? ?]]]].
  deepexec H ltac:(fun H => destruct H as [R [? ?]]).
  progressive_inversion.
  deepexec @per_elem_then_per_top ltac:(fun H => destruct H as [w [? ?]]).
  exists w.
  split; econstructor; eauto.
  erewrite per_ctx_respects_length; try eassumption.
  eexists. symmetry.
  eassumption.
Qed.
