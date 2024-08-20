From Mcltt Require Import Base LibTactics.
From Mcltt.Algorithmic Require Import Subtyping.Definitions.
From Mcltt.Core Require Import NbE.
From Mcltt.Extraction Require Import Evaluation NbE.
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

Theorem subtyping_nf_impl_complete : forall A B,
    {{ ⊢anf A ⊆ B }} ->
    exists H, subtyping_nf_impl A B = left H.
Proof.
  intros.
  destruct (subtyping_nf_impl A B) eqn:Heq; eauto.
  contradiction.
Qed.


Inductive subtyping_order G A B :=
| subtyping_order_run :
  nbe_ty_order G A ->
  nbe_ty_order G B ->
  subtyping_order G A B.
#[local]
  Hint Constructors subtyping_order : mcltt.


Lemma subtyping_order_sound : forall G A B,
    {{ G ⊢a A ⊆ B }} ->
    subtyping_order G A B.
Proof.
  intros * H.
  dependent destruction H.
  mauto using nbe_ty_order_sound.
Qed.

#[local]
  Ltac subtyping_impl_tac1 :=
  match goal with
  | H : subtyping_order _ _ _ |- _ => progressive_invert H
  | H : nbe_ty_order _ _ |- _ => progressive_invert H
  end.

#[local]
  Ltac subtyping_impl_tac :=
  repeat subtyping_impl_tac1; try econstructor; mauto.


#[tactic="subtyping_impl_tac"]
Equations subtyping_impl G A B (H : subtyping_order G A B) :
  { {{G ⊢a A ⊆ B}} } + { ~ {{ G ⊢a A ⊆ B }} } :=
| G, A, B, H =>
    let (a, Ha) := nbe_ty_impl G A _ in
    let (b, Hb) := nbe_ty_impl G B _ in
    match subtyping_nf_impl a b with
    | left _ => left _
    | right _ => right _
    end.
Next Obligation.
  progressive_inversion.
  functional_nbe_rewrite_clear.
  contradiction.
Qed.

Theorem subtyping_impl_complete' : forall G A B,
    {{G ⊢a A ⊆ B}} ->
    forall (H : subtyping_order G A B),
      exists H', subtyping_impl G A B H = left H'.
Proof.
  intros.
  destruct (subtyping_impl G A B H0) eqn:Heq; eauto.
  contradiction.
Qed.

#[local]
 Hint Resolve subtyping_order_sound subtyping_impl_complete' : mcltt.

Theorem subtyping_impl_complete : forall G A B,
    {{G ⊢a A ⊆ B}} ->
    exists H H', subtyping_impl G A B H = left H'.
Proof.
  repeat unshelve mauto.
Qed.
