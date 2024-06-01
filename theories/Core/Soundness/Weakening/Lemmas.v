From Mcltt Require Import Base System.Definitions System.Lemmas Weakening.Definition Presup CtxEq LibTactics.
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


Lemma weakening_conv : forall Γ σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Δ',
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Γ ⊢w σ : Δ' }}.
Proof.
  induction 1; intros; mauto.
  eapply wk_p.
  - eapply IHweakening.
    apply weakening_escape in H.
    gen_presup H.
    progressive_invert HΔ.
    econstructor; [ | | eapply ctxeq_exp | ..]; mauto.
  - mauto.
Qed.

#[export]
 Hint Resolve weakening_conv : mcltt.

Lemma invert_id : forall Γ Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros. remember {{{ Id }}} as σ. revert Heqσ.
  induction H; intros; try congruence; mauto.
Qed.

#[export]
  Instance WfSubPER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.


Lemma weakening_compose : forall Γ' σ' Γ'',
    {{ Γ' ⊢w σ' : Γ'' }} ->
    forall Γ σ,
      {{ Γ ⊢w σ : Γ' }} ->
      {{ Γ ⊢w σ' ∘ σ : Γ'' }}.
Proof.
  induction 1; intros.
  - gen_presup H.
    apply invert_id in Hτ.
    eapply weakening_resp_equiv; [ mauto | ].
    transitivity {{{ Id ∘ σ0 }}}; mauto.
  - eapply wk_p; [eauto |].
    apply weakening_escape in H.
    transitivity {{{ Wk ∘ τ ∘ σ0 }}}; mauto.
Qed.


Lemma weakening_id : forall Γ,
    {{ ⊢ Γ }} ->
    {{ Γ ⊢w Id : Γ }}.
Proof.
  mauto.
Qed.

Lemma weakening_wk : forall Γ T,
    {{ ⊢ Γ , T }} ->
    {{ Γ , T ⊢w Wk : Γ }}.
Proof.
  intros. eapply wk_p; mauto.
Qed.

#[export]
 Hint Resolve weakening_id weakening_wk : mcltt.
