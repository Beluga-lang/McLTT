From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  NatCases
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
From Mcltt.Core.Soundness Require Export LogicalRelation.
From Mcltt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Section soundness_fundamental.

  Theorem soundness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}) /\
      (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊩s σ : Δ }}).
  Proof.
    apply syntactic_wf_mut_ind'; mauto 3.

    - intros.
      assert (exists i, {{ Γ ⊩ A' : Type@i }}) as [] by admit. (* this should be added to the syntactic judgement *)
      mauto.
    - intros.
      assert {{ ⊩ Δ' }} by admit. (* this should be added to the syntactic judgement *)
      mauto.
  Admitted.

  #[local]
  Ltac solve_it := pose proof soundness_fundamental; firstorder.

  Theorem soundness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_sub : forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊩s σ : Δ }}.
  Proof. solve_it. Qed.

End soundness_fundamental.
