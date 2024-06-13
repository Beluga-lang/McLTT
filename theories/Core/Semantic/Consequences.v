From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Readback Soundness.
From Mcltt.Core Require Export System.
Import Domain_Notations.

Lemma adjust_exp_eq_level : forall Γ A A' i j,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A : Type@j }} ->
    {{ Γ ⊢ A' : Type@j }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  intros * ?%completeness ?%soundness ?%soundness.
  destruct_conjs.
  inversion_by_head nbe; subst.
  match_by_head eval_exp ltac:(fun H => directed inversion H; subst; clear H).
  match_by_head read_nf ltac:(fun H => directed inversion H; subst; clear H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [symmetry|]; mautosolve.
Qed.
