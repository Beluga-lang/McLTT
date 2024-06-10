From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import
  Completeness.ContextCases
  Completeness.FunctionCases
  Completeness.NatCases
  Completeness.SubstitutionCases
  Completeness.TermStructureCases
  Completeness.UniverseCases
  Completeness.VariableCases.
From Mcltt.Core Require Export Completeness.LogicalRelation SystemOpt.
Import Domain_Notations.

Section completeness_fundamental.
  Let ctx_prop Γ (_ : {{ ⊢ Γ }}) : Prop := {{ ⊨ Γ }}.
  Let ctx_eq_prop Γ Γ' (_ : {{ ⊢ Γ ≈ Γ' }}) : Prop := {{ ⊨ Γ ≈ Γ' }}.
  Let exp_prop Γ M A (_ : {{ Γ ⊢ M : A }}) : Prop := {{ Γ ⊨ M : A }}.
  Let exp_eq_prop Γ A M M' (_ : {{ Γ ⊢ M ≈ M' : A }}) : Prop := {{ Γ ⊨ M ≈ M' : A }}.
  Let sub_prop Γ σ Δ (_ : {{ Γ ⊢s σ : Δ }}) : Prop := {{ Γ ⊨s σ : Δ }}.
  Let sub_eq_prop Γ Δ σ σ' (_ : {{ Γ ⊢s σ ≈ σ' : Δ }}) : Prop := {{ Γ ⊨s σ ≈ σ' : Δ }}.

  #[local]
  Ltac unfold_prop :=
    unfold ctx_prop, ctx_eq_prop, exp_prop, exp_eq_prop, sub_prop, sub_eq_prop in *;
    clear ctx_prop ctx_eq_prop exp_prop exp_eq_prop sub_prop sub_eq_prop.

  #[local]
  Ltac solve_completeness_fundamental :=
    unfold_prop; mauto; solve [apply valid_ctx_empty | apply valid_exp_var; mauto].

  Theorem completeness_fundamental_ctx : forall Γ (HΓ : {{ ⊢ Γ }}), ctx_prop Γ HΓ.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_ctx_mut_ind
      with
      (P0 := ctx_eq_prop)
      (P1 := exp_prop)
      (P2 := exp_eq_prop)
      (P3 := sub_prop)
      (P4 := sub_eq_prop)...
  Qed.

  Theorem completeness_fundamental_ctx_eq : forall Γ Γ' (HΓΓ' : {{ ⊢ Γ ≈ Γ' }}), ctx_eq_prop Γ Γ' HΓΓ'.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_ctx_eq_mut_ind
      with
      (P := ctx_prop)
      (P1 := exp_prop)
      (P2 := exp_eq_prop)
      (P3 := sub_prop)
      (P4 := sub_eq_prop)...
  Qed.

  Theorem completeness_fundamental_exp : forall Γ M A (HM : {{ Γ ⊢ M : A }}), exp_prop Γ M A HM.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_exp_mut_ind
      with
      (P := ctx_prop)
      (P0 := ctx_eq_prop)
      (P2 := exp_eq_prop)
      (P3 := sub_prop)
      (P4 := sub_eq_prop)...
  Qed.

  Theorem completeness_fundamental_exp_eq : forall Γ M M' A (HMM' : {{ Γ ⊢ M ≈ M' : A }}), exp_eq_prop Γ A M M' HMM'.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_exp_eq_mut_ind
      with
      (P := ctx_prop)
      (P0 := ctx_eq_prop)
      (P1 := exp_prop)
      (P3 := sub_prop)
      (P4 := sub_eq_prop)...
  Qed.

  Theorem completeness_fundamental_sub : forall Γ σ Δ (Hσ : {{ Γ ⊢s σ : Δ }}), sub_prop Γ σ Δ Hσ.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_sub_mut_ind
      with
      (P := ctx_prop)
      (P0 := ctx_eq_prop)
      (P1 := exp_prop)
      (P2 := exp_eq_prop)
      (P4 := sub_eq_prop)...
  Qed.

  Theorem completeness_fundamental_sub_eq : forall Γ σ σ' Δ (Hσσ' : {{ Γ ⊢s σ ≈ σ' : Δ }}), sub_eq_prop Γ Δ σ σ' Hσσ'.
  Proof with solve_completeness_fundamental using.
    induction 1 using wf_sub_eq_mut_ind
      with
      (P := ctx_prop)
      (P0 := ctx_eq_prop)
      (P1 := exp_prop)
      (P2 := exp_eq_prop)
      (P3 := sub_prop)...
  Qed.
End completeness_fundamental.
