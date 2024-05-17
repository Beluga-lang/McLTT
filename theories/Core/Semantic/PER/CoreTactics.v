From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mcltt Require Import Base Evaluation LibTactics PER.Definitions Readback.
Import Domain_Notations.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : {{ Dom ~?c ≈ ~?c' ∈ ?in_rel0 }} |- _ =>
        tryif (unify in_rel0 in_rel)
        then (destruct (H _ _ H') as []; destruct_all; mark_with H' 1)
        else fail
    end;
  unmark_all_with 1.
Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.
Ltac destruct_rel_typ :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_typ _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.

(** Universe/Element PER Helper Tactics *)

Ltac invert_per_univ_elem H :=
  simp per_univ_elem in H;
  inversion H;
  subst;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac per_univ_elem_econstructor :=
  simp per_univ_elem;
  econstructor;
  try rewrite <- per_univ_elem_equation_1 in *.
