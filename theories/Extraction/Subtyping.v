From Mcltt Require Import Base LibTactics.
From Mcltt.Algorithmic Require Import Subtyping.Definitions.
From Mcltt.Core Require Import NbE.
From Mcltt.Extraction Require Import NbE.
From Equations Require Import Equations.
Import Domain_Notations.


Equations subtyping_nf_impl (A B : nf) : bool :=
| n{{{ Type@i }}}, n{{{ Type@j }}} with Compare_dec.le_lt_dec i j => {
  | left _ => true;
  | right _ => false
  }
| n{{{ Π A B }}}, n{{{ Π A' B' }}} with nf_eq_dec A A' => {
  | left _ => subtyping_nf_impl B B'
  | right _ => false
  }
| A, B with nf_eq_dec A B => {
  | left _ => true
  | right _ => false
  }.

Theorem subtyping_nf_impl_sound : forall A B,
    subtyping_nf_impl A B = true ->
    alg_subtyping_nf A B.
Proof.
  intros. funelim (subtyping_nf_impl A B); mauto 2.
  all:simp subtyping_nf_impl in *;
    repeat match goal with
      | H : _ = _ |- _ => rewrite H in *
      end;
    subst;
    simpl in *;
    try congruence.
  all:try solve [econstructor; simpl; trivial].
  mauto.
Qed.

Theorem subtyping_nf_impl_complete : forall A B,
    alg_subtyping_nf A B ->
    subtyping_nf_impl A B = true.
Proof.
  induction 1; subst.
  - destruct (nf_eq_dec N N) eqn:?; try congruence.
    destruct N; simp subtyping_nf_impl;
      try rewrite Heqs;
      simpl in *;
      try contradiction;
      trivial.
  - simp subtyping_nf_impl.
    destruct (Compare_dec.le_lt_dec i j);
      simpl; lia.
  - simp subtyping_nf_impl.
    destruct (nf_eq_dec A' A'); simpl; congruence.
Qed.


(* Equations subtyping_impl Γ A B : bool := *)
(* | Γ, A, B => { *)
(*     let (w, _) := nbe_impl Γ  *)
(*   } *)
