From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Semantic Require Import NbE.
From Mcltt.Core.Soundness Require Import LogicalRelation FundamentalTheorem.
From Mcltt.Core.Syntactic Require Import SystemOpt.
Import Domain_Notations.

Theorem soundness : forall {Γ M A},
  {{ Γ ⊢ M : A }} ->
  exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Admitted.
