From Coq Require Import RelationClasses.
From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core Require Export Completeness.
From Mcltt.Core.Semantic Require Import Realizability.
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
