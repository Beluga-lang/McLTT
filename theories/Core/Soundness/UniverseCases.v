From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_typ : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ Type@i : Type@(S i) }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_typ : mcltt.
