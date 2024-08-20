From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_pi : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Π A B : Type@i }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_pi : mcltt.

Lemma glu_rel_exp_fn : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_fn : mcltt.

Lemma glu_rel_exp_app : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_app : mcltt.
