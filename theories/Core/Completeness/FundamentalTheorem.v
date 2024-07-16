From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import
  Completeness.ContextCases
  Completeness.FunctionCases
  Completeness.NatCases
  Completeness.SubstitutionCases
  Completeness.TermStructureCases
  Completeness.UniverseCases
  Completeness.VariableCases
  Completeness.SubtypingCases.
From Mcltt.Core Require Export Completeness.LogicalRelation SystemOpt.
Import Domain_Notations.

Section completeness_fundamental.

  Theorem completeness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⊨ Γ }}) /\
      (forall Γ Γ', {{ ⊢ Γ ⊆ Γ' }} -> {{ SubE Γ <: Γ' }}) /\
      (forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊨ M : A }}) /\
      (forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ ⊨ M ≈ M' : A }}) /\
      (forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊨s σ : Δ }}) /\
      (forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ Γ ⊨s σ ≈ σ' : Δ }}) /\
      (forall Γ A A', {{ Γ ⊢ A ⊆ A' }} -> {{ Γ ⊨ A ⊆ A' }}).
  Proof.
    apply syntactic_wf_mut_ind;
      mauto 3.
    intros.
    apply valid_exp_var;
      mauto.
  Qed.

  #[local]
   Ltac solve_it := pose proof completeness_fundamental; firstorder.


  Theorem completeness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⊨ Γ }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_ctx_sub : forall Γ Γ', {{ ⊢ Γ ⊆ Γ' }} -> {{ SubE Γ <: Γ' }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊨ M : A }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_exp_eq : forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ ⊨ M ≈ M' : A }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_sub : forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊨s σ : Δ }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_sub_eq : forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ Γ ⊨s σ ≈ σ' : Δ }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_subtyp : forall Γ A A', {{ Γ ⊢ A ⊆ A' }} -> {{ Γ ⊨ A ⊆ A' }}.
  Proof. solve_it. Qed.

  Theorem completeness_fundamental_ctx_eq : forall Γ Γ', {{ ⊢ Γ ≈ Γ' }} -> {{ ⊨ Γ ≈ Γ' }}.
  Proof.
    induction 1.
    - apply valid_ctx_empty.
    - apply completeness_fundamental_exp_eq in H2.
      mauto.
  Qed.

End completeness_fundamental.
