From Equations Require Import Equations.

From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions.

Ltac glu_univ_elem_econstructor :=
  progress simp glu_univ_elem;
  econstructor;
  try rewrite <- glu_univ_elem_equation_1 in *.
