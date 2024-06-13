From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Completeness.FundamentalTheorem Completeness.LogicalRelation Semantic.Realizability.
From Mcltt.Core Require Export SystemOpt.
Import Domain_Notations.

Lemma exp_eq_typ_implies_eq_level : forall {Γ i j k},
    {{ Γ ⊢ Type@i ≈ Type@j : Type@k }} ->
    i = j.
Proof with mautosolve.
  intros * H.
  assert {{ Γ ⊨ Type@i ≈ Type@j : Type@k }} as [env_relΓ] by eauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p [? [? []]]] by eauto using per_ctx_then_per_env_initial_env.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  destruct_conjs.
  match_by_head1 per_univ_elem invert_per_univ_elem.
  reflexivity.
Qed.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level : mcltt.

Theorem not_exp_eq_typ_nat : forall Γ i j,
    ~ {{ Γ ⊢ ℕ ≈ Type@i : Type@j }}.
Proof.
  intros ** ?.
  assert {{ Γ ⊨ ℕ ≈ Type@i : Type@j }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  destruct_conjs.
  match_by_head1 per_univ_elem invert_per_univ_elem.
Qed.

#[export]
Hint Resolve not_exp_eq_typ_nat : mcltt.

Theorem not_exp_eq_typ_pi : forall Γ i A B j,
    ~ {{ Γ ⊢ Π A B ≈ Type@i : Type@j }}.
Proof.
  intros ** ?.
  assert {{ Γ ⊨ Π A B ≈ Type@i : Type@j }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  destruct_conjs.
  match_by_head1 per_univ_elem invert_per_univ_elem.
Qed.

#[export]
Hint Resolve not_exp_eq_typ_pi : mcltt.

Lemma typ_subsumption_spec : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⊢ Γ }} /\ exists j, {{ Γ ⊢ A ≈ A' : Type@j }} \/ exists i i', i < i' /\ {{ Γ ⊢ Type@i ≈ A : Type@j }} /\ {{ Γ ⊢ A' ≈ Type@i' : Type@j }}.
Proof.
  intros * H.
  dependent induction H; split; mauto 3.
  - (* typ_subsumption_typ *)
    eexists.
    right.
    do 2 eexists.
    repeat split; revgoals; mauto.
  - (* typ_subsumption_trans *)
    destruct IHtyp_subsumption1 as [? [? [| [i1 [i1']]]]]; destruct IHtyp_subsumption2 as [? [? [| [i2 [i2']]]]];
      destruct_conjs;
      only 1: mautosolve 4;
      eexists; right; do 2 eexists.
    + (* left & right *)
      split; [eassumption |].
      solve [mauto using lift_exp_eq_max_left].
    + (* right & left *)
      split; [eassumption |].
      solve [mauto using lift_exp_eq_max_right].
    + exvar nat ltac:(fun j => assert {{ Γ ⊢ Type@i2 ≈ Type@i1' : Type@j }} by mauto).
      replace i2 with i1' in * by mauto.
      split; [etransitivity; revgoals; eassumption |].
      mauto 4 using lift_exp_eq_max_left, lift_exp_eq_max_right.
Qed.

#[export]
Hint Resolve typ_subsumption_spec : mcltt.

Lemma typ_subsumption_typ_spec : forall {Γ i i'},
    {{ Γ ⊢ Type@i ⊆ Type@i' }} ->
    {{ ⊢ Γ }} /\ i <= i'.
Proof with mautosolve.
  intros * [? [j [| [i0 [i0']]]]]%typ_subsumption_spec.
  - (* when lhs is equivalent to rhs *)
    replace i with i' in *...
  - (* when lhs is (strictly) subsumed by rhs *)
    destruct_conjs.
    (on_all_hyp: fun H => apply exp_eq_typ_implies_eq_level in H); subst.
    split; [| lia]...
Qed.

#[export]
Hint Resolve typ_subsumption_typ_spec : mcltt.
