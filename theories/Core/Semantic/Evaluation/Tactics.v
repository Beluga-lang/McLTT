From Mcltt Require Import Base LibTactics Evaluation.Definitions Evaluation.Lemmas.
Import Domain_Notations.

Ltac simplify_evals :=
  functional_eval_rewrite_clear;
  clear_dups;
  repeat (match_by_head eval_exp ltac:(fun H => directed inversion H; subst; clear H)
          || match_by_head eval_sub ltac:(fun H => directed inversion H; subst; clear H));
  functional_eval_rewrite_clear;
  clear_dups.
