From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Semantic.Realizability Completeness.Consequences.Types.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Domain_Notations.

Corollary wf_zero_inversion : forall Γ A,
    {{ Γ ⊢ zero : A }} ->
    exists i, {{ Γ ⊢ ℕ ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H; try mautosolve.
  - (* wf_conv *)
    assert (exists i : nat, {{ Γ ⊢ ℕ ≈ A : Type@i }}) as [j] by eauto...
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
    destruct_conjs...
  - (* wf_cumu *)
    assert ({{ Γ ⊢ M : ℕ }} /\ exists j : nat, {{ Γ ⊢ ℕ ≈ Type@i : Type@j }}) as [? [? contra]] by eauto.
    contradict contra...
Qed.

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
