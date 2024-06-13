From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Completeness.FundamentalTheorem Completeness.LogicalRelation Semantic.Realizability.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Domain_Notations.

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

Corollary wf_zero_inversion : forall Γ A,
    {{ Γ ⊢ zero : A }} ->
    exists i, {{ Γ ⊢ ℕ ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H; try mautosolve.
  - (* wf_conv *)
    assert (exists i : nat, {{ Γ ⊢ ℕ ≈ A : Type@i }}) as [j] by eauto.
    mauto using lift_exp_eq_max_left, lift_exp_eq_max_right.
  - (* wf_cumu *)
    assert (exists j : nat, {{ Γ ⊢ ℕ ≈ Type@i : Type@j }}) as [j contra] by eauto.
    contradict contra...
Qed.

Corollary wf_succ_inversion : forall Γ A M,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ exists i, {{ Γ ⊢ ℕ ≈ A : Type@i }}.
Proof with mautosolve.
  intros * H.
  dependent induction H; try (split; mautosolve).
  - (* wf_conv *)
    assert ({{ Γ ⊢ M : ℕ }} /\ exists i : nat, {{ Γ ⊢ ℕ ≈ A : Type@i }}) as [] by eauto.
    destruct_conjs.
    mauto 6 using lift_exp_eq_max_left, lift_exp_eq_max_right.
  - (* wf_cumu *)
    assert ({{ Γ ⊢ M : ℕ }} /\ exists j : nat, {{ Γ ⊢ ℕ ≈ Type@i : Type@j }}) as [? [? contra]] by eauto.
    contradict contra...
Qed.

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

Corollary wf_fn_inversion : forall {Γ A M C},
    {{ Γ ⊢ λ A M : C }} ->
    exists i B, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }} /\ {{ Γ ⊢ Π A B ≈ C : Type@i }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H.
  - (* wf_fn *)
    gen_presups.
    exvar nat ltac:(fun i => assert {{ Γ ⊢ A : Type @ i }} by (eapply lift_exp_max_left; eauto)).
    exvar nat ltac:(fun i => assert {{ Γ, A ⊢ B : Type @ i }} by (eapply lift_exp_max_right; eauto)).
    do 2 eexists.
    repeat split...
  - (* wf_conv *)
    specialize (IHwf_exp _ _ eq_refl) as [i0 [? [? []]]].
    exists (max i i0).
    eexists.
    repeat split;
      mauto 4 using lift_exp_max_right, lift_exp_eq_max_left, lift_exp_eq_max_right.
  - (* wf_cumu *)
    specialize (IHwf_exp _ _ eq_refl) as [? [? [? [? contra]]]].
    contradict contra...
Qed.
