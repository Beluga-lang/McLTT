From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation PER System.
Import Domain_Notations.

Ltac eexists_rel_exp :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_rel_subst :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].

Ltac invert_rel_typ_body :=
  dir_inversion_by_head eval_exp; subst;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H); subst;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  try rewrite <- per_univ_elem_equation_1 in *.
