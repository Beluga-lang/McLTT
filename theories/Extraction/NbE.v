From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Readback Evaluation NbE.
From Mcltt.Extraction Require Import Evaluation Readback.
From Equations Require Import Equations.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env_order : ctx -> Prop :=
| ie_nil : initial_env_order nil
| ie_cons :
  `( initial_env_order Γ ->
     (forall p, initial_env Γ p ->
           eval_exp_order A p) ->
     initial_env_order (A :: Γ)).

#[local]
  Hint Constructors initial_env_order : mcltt.

Lemma initial_env_order_sound : forall Γ p,
    initial_env Γ p ->
    initial_env_order Γ.
Proof with (econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto).
  induction 1...
Qed.

#[local]
  Hint Resolve initial_env_order_sound : mcltt.

Derive Signature for initial_env_order.

#[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : initial_env_order _ |- _ => progressive_invert H
  end.

#[local]
  Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

#[tactic="impl_obl_tac"]
  Equations initial_env_impl G (H : initial_env_order G) : { p | initial_env G p } by struct H :=
| nil, H => exist _ empty_env _
| cons A G, H =>
    let (p, Hp) := initial_env_impl G _ in
    let (a, Ha) := eval_exp_impl A p _ in
    exist _ d{{{ p ↦ ⇑! a (length G) }}} _.


Lemma initial_env_impl_complete' : forall G p,
    initial_env G p ->
    forall (H : initial_env_order G),
      exists H', initial_env_impl G H = exist _ p H'.
Proof.
  induction 1;
    pose proof eval_exp_impl_complete';
    intros; simp initial_env_impl;
    do 2 try complete_tac;
    eauto.
Qed.

#[local]
  Hint Resolve initial_env_impl_complete' : mcltt.


Lemma initial_env_impl_complete : forall G p,
    initial_env G p ->
    exists H H', initial_env_impl G H = exist _ p H'.
Proof.
  repeat unshelve mauto.
Qed.
