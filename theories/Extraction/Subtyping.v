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



(* Equations subtyping_impl Γ A B : bool := *)
(* | Γ, A, B => { *)
(*     let (w, _) := nbe_impl Γ  *)
(*   } *)
