From Coq Require Import Program.Equality.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Soundness.Weakening Require Import Definitions.
From Mcltt.Core.Syntactic Require Export Corollaries.
Import Syntax_Notations.

Lemma weakening_escape : forall Γ σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  induction 1;
    match goal with
    | H : _ |- _ =>
        solve [gen_presup H; trivial]
    end.
Qed.

#[export]
Hint Resolve weakening_escape : mcltt.


Ltac saturate_weakening_escape1 :=
  match goal with
  | H : {{ ^_ ⊢w ^_ : ^_ }} |- _ =>
      pose proof (weakening_escape _ _ _ H);
      fail_if_dup
  end.

Ltac saturate_weakening_escape :=
  repeat saturate_weakening_escape1.

Lemma weakening_resp_equiv : forall Γ σ σ' Δ,
    {{ Γ ⊢w σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢w σ' : Δ }}.
Proof.
  induction 1; mauto.
Qed.

Lemma ctxeq_weakening : forall Γ σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Γ',
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢w σ : Δ }}.
Proof.
  induction 1; mauto.
Qed.

Lemma ctxsub_weakening : forall Γ σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Δ',
      {{ ⊢ Δ ⊆ Δ' }} ->
      {{ Γ ⊢w σ : Δ' }}.
Proof.
  induction 1; mauto.
Qed.

Lemma weakening_conv : forall Γ σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Δ',
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Γ ⊢w σ : Δ' }}.
Proof.
  intros; mauto using ctxsub_weakening.
Qed.

#[export]
Hint Resolve ctxsub_weakening weakening_conv : mcltt.

Lemma weakening_compose : forall Γ' σ' Γ'',
    {{ Γ' ⊢w σ' : Γ'' }} ->
    forall Γ σ,
      {{ Γ ⊢w σ : Γ' }} ->
      {{ Γ ⊢w σ' ∘ σ : Γ'' }}.
Proof with mautosolve.
  induction 1; intros.
  - gen_presup H.
    assert {{ ⊢ Γ ⊆ Δ }} by mauto.
    eapply weakening_resp_equiv; [mauto 2 |].
    transitivity {{{ Id ∘ σ0 }}}...
  - eapply wk_p; eauto.
    transitivity {{{ (Wk ∘ τ) ∘ σ0 }}}; mauto 4.
    eapply wf_sub_eq_compose_assoc; revgoals...
Qed.

#[export]
Hint Resolve weakening_compose : mcltt.

Lemma weakening_id : forall Γ,
    {{ ⊢ Γ }} ->
    {{ Γ ⊢w Id : Γ }}.
Proof.
  mauto.
Qed.

Lemma weakening_wk : forall Γ A,
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢w Wk : Γ }}.
Proof.
  intros.
  econstructor; mautosolve.
Qed.

#[export]
Hint Resolve weakening_id weakening_wk : mcltt.
