From Equations Require Import Equations.

From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions.

Ltac basic_invert_glu_univ_elem H :=
  progress simp glu_univ_elem in H;
  inversion H;
  subst;
  try rewrite <- glu_univ_elem_equation_1 in *.

Ltac basic_glu_univ_elem_econstructor :=
  progress simp glu_univ_elem;
  econstructor;
  try rewrite <- glu_univ_elem_equation_1 in *.
