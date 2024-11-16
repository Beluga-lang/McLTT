From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.Evaluation Require Import Definitions Lemmas.
Import Domain_Notations.

Ltac simplify_evals :=
  functional_eval_rewrite_clear;
  clear_dups;
  repeat (match_by_head eval_exp ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_app ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_natrec ltac:(fun H => directed dependent destruction H)
          || match_by_head eval_sub ltac:(fun H => directed dependent destruction H));
  functional_eval_rewrite_clear;
  clear_dups.
