From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.FundamentalTheorem Semantic.Realizability.
From Mcltt.Core Require Export Semantic.NbE SystemOpt.
Import Domain_Notations.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  rename x into elem_rel.
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable...
Qed.

(* Theorem completeness_for_typ_subsumption : forall {Γ A A'}, *)
(*   {{ Γ ⊢ A ⊆ A' }} -> *)
(*   exists i W W', nbe Γ A {{{ Type@i }}} W /\ nbe Γ A' {{{ Type@i }}} W' /\ nf_subsumption W W'. *)
(* Proof. *)
(*   induction 1. *)
(*   - assert {{ ⊨ Γ }} as [env_relΓ] by eauto using completeness_fundamental_ctx. *)
(*     assert (exists p p' : env, initial_env Γ p /\ initial_env Γ p' /\ env_relΓ p p') by eauto using per_ctx_then_per_env_initial_env. *)
(*     destruct_conjs. *)
(*     functional_initial_env_rewrite_clear. *)
(*     exists (S (S i)); do 2 eexists; repeat split; mauto. *)
(*   - assert (exists W, nbe Γ A {{{ Type@i }}} W /\ nbe Γ A' {{{ Type@i }}} W) as [? []] by eauto using completeness. *)
(*     do 3 eexists; repeat split; mauto. *)
(*   - destruct IHtyp_subsumption1 as [i1]. *)
(*     destruct IHtyp_subsumption2 as [i2]. *)
(*     destruct_conjs. *)
(*     functional_nbe_rewrite_clear. *)
(*     exvar nf ltac:(fun W => assert (nbe Γ A {{{ Type@(max i1 i2) }}} W) by mauto using lift_nbe_max_left). *)
(*     exvar nf ltac:(fun W => assert (nbe Γ A' {{{ Type@(max i1 i2) }}} W) by mauto using lift_nbe_max_left). *)
(*     exvar nf ltac:(fun W => assert (nbe Γ A'' {{{ Type@(max i1 i2) }}} W) by mauto using lift_nbe_max_right). *)
(*     do 3 eexists; repeat split; mauto. *)
(*     etransitivity; eassumption. *)
(* Qed. *)
