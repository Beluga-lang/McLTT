From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Semantic.Domain Semantic.NbE System.
Import Domain_Notations.

Theorem soundness : forall {Γ M A},
  {{ Γ ⊢ M : A }} ->
  exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Admitted.
