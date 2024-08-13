From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_vlookup : forall {Γ x A},
    {{ ⊩ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊩ #x : A }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcltt.

Lemma glu_rel_exp_sub : forall {Γ σ Δ M A},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ M : A }} ->
    {{ Γ ⊩ M[σ] : A[σ] }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_sub : mcltt.
