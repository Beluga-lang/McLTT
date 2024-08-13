From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_nat : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ ℕ : Type@i }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_nat : mcltt.

Lemma glu_rel_exp_zero : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ zero : ℕ }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_zero : mcltt.

Lemma glu_rel_exp_succ : forall {Γ M},
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ succ M : ℕ }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_succ : mcltt.

Lemma glu_rel_exp_natrec : forall {Γ A i MZ MS M},
    {{ Γ , ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊩ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_natrec : mcltt.
