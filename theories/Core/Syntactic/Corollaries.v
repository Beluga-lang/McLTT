From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import CtxEq Presup.
Import Syntax_Notations.

Corollary invert_id : forall Γ Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H; mauto.
Qed.

#[export]
Hint Resolve invert_id : mcltt.

Corollary sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A [ Id ] }}.
Proof.
  intros.
  gen_presups.
  mauto 6.
Qed.

#[export]
Hint Resolve sub_id_typ : mcltt.

Corollary invert_sub_id : forall Γ M A,
    {{ Γ ⊢ M [ Id ] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * H.
  dependent induction H; mauto.
Qed.

#[export]
Hint Resolve invert_sub_id : mcltt.
