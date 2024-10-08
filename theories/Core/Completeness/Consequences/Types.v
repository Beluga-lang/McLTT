From Coq Require Import RelationClasses.
From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core Require Export Completeness.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Syntactic Require Export SystemOpt.
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
| var_is_typ_constr : forall x, is_typ_constr {{{ #x }}}
.
#[export]
Hint Constructors is_typ_constr : mcltt.  

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var : forall Γ A x i,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ #x : Type@i }} ->
    A = {{{ #x }}}.
Proof.
  intros * Histyp ?.
  assert {{ Γ ⊨ A ≈ #x : Type@i }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  gen_presups.
  assert (exists A, {{ #x : A ∈ Γ }} /\ {{ Γ ⊢ A ⊆ Type@i }}) as [? [? _]] by mauto 2.
  assert (exists a, ρ x = d{{{ ⇑! a (length Γ - x - 1) }}}) as [? Heq] by mauto 2.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    rewrite Heq in *;
    match_by_head1 per_univ_elem invert_per_univ_elem.
  rename x1 into a0.
  rename x2 into x1.
  assert (exists A, {{ #x1 : A ∈ Γ }} /\ {{ Γ ⊢ A ⊆ Type@i }}) as [? [? _]] by mauto 2.
  assert (exists a, ρ x1 = d{{{ ⇑! a (length Γ - x1 - 1) }}}) as [a1] by mauto 2.
  assert (x0 < length Γ) by mauto 2.
  assert (x1 < length Γ) by mauto 2.
  f_equal.
  enough (length Γ - x0 - 1 = length Γ - x1 - 1) by lia.
  replace (ρ x1) with d{{{ ⇑! a1 (length Γ - x1 - 1) }}} in * by intuition.
  autoinjections.
  match_by_head1 per_bot ltac:(fun H => destruct (H (length Γ)) as [? []]).
  match_by_head read_ne ltac:(fun H => directed dependent destruction H).
  lia.
Qed.
#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mcltt.

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
  - reflexivity.
  - replace {{{ #x0 }}} with {{{ Type@i }}} by mauto 3 using is_typ_constr_and_exp_eq_var_implies_eq_var.
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
  - reflexivity.
  - replace {{{ #x0 }}} with {{{ ℕ }}} by mauto 3 using is_typ_constr_and_exp_eq_var_implies_eq_var.
    reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mcltt.
