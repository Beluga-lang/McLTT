From Mcltt Require Import Base LibTactics.
From Mcltt.Algorithmic Require Import Subtyping.Definitions.
From Mcltt.Core Require Import NbE.
From Mcltt.Extraction Require Import NbE.
From Equations Require Import Equations.
Import Domain_Notations.


#[local]
  Ltac subtyping_tac :=
  lazymatch goal with
  | |- {{ ⊢anf ~_ ⊆ ~_ }} =>
      subst;
      mauto 4;
      try congruence;
      econstructor; simpl; trivial
  | |- ~ {{ ⊢anf ~_ ⊆ ~_ }} =>
      let H := fresh "H" in
      intro H; dependent destruction H; simpl in *;
      try lia;
      try congruence
  end.

#[tactic="subtyping_tac"]
Equations subtyping_nf_impl A B : { {{ ⊢anf A ⊆ B }} } + {~ {{ ⊢anf A ⊆ B }} } :=
| n{{{ Type@i }}}, n{{{ Type@j }}} with Compare_dec.le_lt_dec i j => {
  | left _ => left _;
  | right _ => right _
  }
| n{{{ Π A B }}}, n{{{ Π A' B' }}} with nf_eq_dec A A' => {
  | left _ with subtyping_nf_impl B B' => {
    | left _ => left _
    | right _ => right _
    }
  | right _ => right _
  }
| A, B with nf_eq_dec A B => {
  | left _ => left _
  | right _ => right _
  }.


Inductive subtyping_order G A B :=
| subtyping_order_run :
  nbe_ty_order G A ->
  nbe_ty_order G B ->
  subtyping_order G A B.
#[local]
  Hint Constructors subtyping_order : mcltt.

#[local]
  Ltac subtyping_impl_tac1 :=
  match goal with
  | H : subtyping_order _ _ _ |- _ => progressive_invert H
  end.

#[local]
  Ltac subtyping_impl_tac :=
  repeat subtyping_impl_tac1; try econstructor; mauto.

Equations? subtyping_impl G A B (H1 : nbe_ty_order G A) (H2 : nbe_ty_order G B) :
  { {{G ⊢a A ⊆ B}} } + { ~ {{ G ⊢a A ⊆ B }} } :=
| G, A, B with nbe_ty_impl G A H1 => {
  | @exist a _ with nbe_ty_impl G B H2 => {
    | @exist b _ with subtyping_nf_impl a b => {
      | left _ => _;
      | right _ => _
      }
    }
  }.
