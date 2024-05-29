From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.FundamentalTheorem Semantic.NbE Semantic.Realizability System.
Import Domain_Notations.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p] by (apply per_ctx_then_per_env_initial_env; eauto).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  rename x into elem_rel.
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable...
Qed.
