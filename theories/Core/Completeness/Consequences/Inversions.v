From Coq Require Import RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness Semantic.Realizability Completeness.Consequences.Types.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Domain_Notations.

Corollary wf_zero_inversion' : forall Γ A,
    {{ Γ ⊢ zero : A }} ->
    exists i, {{ Γ ⊢ ℕ ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros * []%wf_zero_inversion%typ_subsumption_left_nat...
Qed.

#[export]
Hint Resolve wf_zero_inversion' : mcltt.

Corollary wf_succ_inversion' : forall Γ A M,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ exists i, {{ Γ ⊢ ℕ ≈ A : Type@i }}.
Proof with mautosolve.
  intros * [? []%typ_subsumption_left_nat]%wf_succ_inversion...
Qed.

#[export]
Hint Resolve wf_succ_inversion' : mcltt.

Corollary wf_fn_inversion' : forall {Γ A M C},
    {{ Γ ⊢ λ A M : C }} ->
    exists B, {{ Γ, A ⊢ M : B }} /\ exists i, {{ Γ ⊢ Π A B ≈ C : Type@i }}.
Proof with mautosolve.
  intros * [? [? []%typ_subsumption_left_pi]]%wf_fn_inversion...
Qed.

#[export]
Hint Resolve wf_fn_inversion' : mcltt.
