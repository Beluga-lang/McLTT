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

Inductive is_typ_constr : typ -> Prop :=
| typ_is_typ_constr : forall i, is_typ_constr {{{ Type@i }}}
| nat_is_typ_constr : is_typ_constr {{{ ℕ }}}
| pi_is_typ_constr : forall A B, is_typ_constr {{{ Π A B }}}
.

#[export]
Hint Constructors is_typ_constr : mcltt.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ : forall Γ A i j,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ Type@i : Type@j }} ->
    A = {{{ Type@i }}}.
Proof.
  intros * Histyp ?.
  assert {{ Γ ⊨ A ≈ Type@i : Type@j }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    match_by_head1 per_univ_elem invert_per_univ_elem.
  reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mcltt.

Theorem is_typ_constr_and_exp_eq_nat_implies_eq_nat : forall Γ A j,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ ℕ : Type@j }} ->
    A = {{{ ℕ }}}.
Proof.
  intros * Histyp ?.
  assert {{ Γ ⊨ A ≈ ℕ : Type@j }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    match_by_head1 per_univ_elem invert_per_univ_elem.
  reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mcltt.

(* We cannot use this spec as the definition of [typ_subsumption] as
   then its transitivity requires [exp_eq_typ_implies_eq_level] or a similar semantic lemma *)
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

Lemma not_typ_and_typ_subsumption_left_typ_constr_implies_exp_eq : forall {Γ A A'},
    is_typ_constr A ->
    (forall i, A <> {{{ Type@i }}}) ->
    {{ Γ ⊢ A ⊆ A' }} ->
    exists j, {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  intros * ? ? H%typ_subsumption_spec.
  destruct_all; mauto.
  exfalso.
  intuition.
  mauto using is_typ_constr_and_exp_eq_typ_implies_eq_typ.
Qed.

#[export]
Hint Resolve not_typ_and_typ_subsumption_left_typ_constr_implies_exp_eq : mcltt.

Lemma not_typ_and_typ_subsumption_right_typ_constr_implies_exp_eq : forall {Γ A A'},
    is_typ_constr A' ->
    (forall i, A' <> {{{ Type@i }}}) ->
    {{ Γ ⊢ A ⊆ A' }} ->
    exists j, {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  intros * ? ? H%typ_subsumption_spec.
  destruct_all; mauto.
  exfalso.
  intuition.
  mauto using is_typ_constr_and_exp_eq_typ_implies_eq_typ.
Qed.

#[export]
Hint Resolve not_typ_and_typ_subsumption_right_typ_constr_implies_exp_eq : mcltt.

Corollary typ_subsumption_left_nat : forall {Γ A'},
    {{ Γ ⊢ ℕ ⊆ A' }} ->
    exists j, {{ Γ ⊢ ℕ ≈ A' : Type@j }}.
Proof.
  intros * H%not_typ_and_typ_subsumption_left_typ_constr_implies_exp_eq; mauto.
  congruence.
Qed.

#[export]
Hint Resolve typ_subsumption_left_nat : mcltt.

Corollary typ_subsumption_left_pi : forall {Γ A B C'},
    {{ Γ ⊢ Π A B ⊆ C' }} ->
    exists j, {{ Γ ⊢ Π A B ≈ C' : Type@j }}.
Proof.
  intros * H%not_typ_and_typ_subsumption_left_typ_constr_implies_exp_eq; mauto.
  congruence.
Qed.

#[export]
Hint Resolve typ_subsumption_left_pi : mcltt.

Corollary typ_subsumption_left_typ : forall {Γ i A'},
    {{ Γ ⊢ Type@i ⊆ A' }} ->
    exists j i', i <= i' /\ {{ Γ ⊢ A' ≈ Type@i' : Type@j }}.
Proof.
  intros * H%typ_subsumption_spec.
  destruct_all; mauto.
  (on_all_hyp: fun H => apply exp_eq_typ_implies_eq_level in H); subst.
  mauto using PeanoNat.Nat.lt_le_incl.
Qed.

#[export]
Hint Resolve typ_subsumption_left_typ : mcltt.

Corollary typ_subsumption_right_nat : forall {Γ A},
    {{ Γ ⊢ A ⊆ ℕ }} ->
    exists j, {{ Γ ⊢ A ≈ ℕ : Type@j }}.
Proof.
  intros * H%not_typ_and_typ_subsumption_right_typ_constr_implies_exp_eq; mauto.
  congruence.
Qed.

#[export]
Hint Resolve typ_subsumption_right_nat : mcltt.

Corollary typ_subsumption_right_pi : forall {Γ C A' B'},
    {{ Γ ⊢ C ⊆ Π A' B' }} ->
    exists j, {{ Γ ⊢ C ≈ Π A' B' : Type@j }}.
Proof.
  intros * H%not_typ_and_typ_subsumption_right_typ_constr_implies_exp_eq; mauto.
  congruence.
Qed.

#[export]
Hint Resolve typ_subsumption_right_pi : mcltt.

Corollary typ_subsumption_right_typ : forall {Γ A i'},
    {{ Γ ⊢ A ⊆ Type@i' }} ->
    exists j i, i <= i' /\ {{ Γ ⊢ Type@i ≈ A : Type@j }}.
Proof.
  intros * H%typ_subsumption_spec.
  destruct_all; mauto.
  (on_all_hyp: fun H => apply exp_eq_typ_implies_eq_level in H); subst.
  mauto using PeanoNat.Nat.lt_le_incl.
Qed.

#[export]
Hint Resolve typ_subsumption_right_typ : mcltt.

Corollary typ_subsumption_typ_spec : forall {Γ i i'},
    {{ Γ ⊢ Type@i ⊆ Type@i' }} ->
    {{ ⊢ Γ }} /\ i <= i'.
Proof with mautosolve.
  intros * H.
  pose proof (typ_subsumption_left_typ H).
  destruct_conjs.
  (on_all_hyp: fun H => apply exp_eq_typ_implies_eq_level in H); subst...
Qed.

#[export]
Hint Resolve typ_subsumption_typ_spec : mcltt.
