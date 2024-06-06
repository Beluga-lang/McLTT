From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation PER System.
Import Domain_Notations.

Ltac eexists_rel_exp :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_rel_sub :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].

Ltac simplify_evals :=
  functional_eval_rewrite_clear;
  clear_dups;
  repeat (match_by_head eval_exp ltac:(fun H => directed inversion H; subst; clear H)
          || match_by_head eval_sub ltac:(fun H => directed inversion H; subst; clear H));
  functional_eval_rewrite_clear;
  clear_dups.

Ltac invert_rel_typ_body :=
  simplify_evals;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  clear_dups;
  try rewrite <- per_univ_elem_equation_1 in *.
