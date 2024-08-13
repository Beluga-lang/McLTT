From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_sub_id : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩s Id : Γ }}.
Admitted.

#[export]
Hint Resolve glu_rel_sub_id : mcltt.

Lemma glu_rel_sub_weaken : forall {Γ A},
    {{ ⊩ Γ, A }} ->
    {{ Γ, A ⊩s Wk : Γ }}.
Admitted.

#[export]
Hint Resolve glu_rel_sub_weaken : mcltt.

Lemma glu_rel_sub_compose : forall {Γ1 σ2 Γ2 σ1 Γ3},
    {{ Γ1 ⊩s σ2 : Γ2 }} ->
    {{ Γ2 ⊩s σ1 : Γ3 }} ->
    {{ Γ1 ⊩s σ1 ∘ σ2 : Γ3 }}.
Admitted.

#[export]
Hint Resolve glu_rel_sub_compose : mcltt.

Lemma glu_rel_sub_extend : forall {Γ σ Δ M A i},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A[σ] }} ->
    {{ Γ ⊩s (σ ,, M) : Δ , A }}.
Admitted.

#[export]
Hint Resolve glu_rel_sub_extend : mcltt.
