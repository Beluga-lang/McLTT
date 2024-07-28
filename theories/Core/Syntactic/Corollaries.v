From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics CtxSub.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Syntax_Notations.

Corollary sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A [ Id ] }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve sub_id_typ : mcltt.

Corollary invert_sub_id : forall Γ M A,
    {{ Γ ⊢ M [ Id ] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcltt.

Add Parametric Morphism i Γ Δ : a_sub
    with signature wf_exp_eq Δ {{{ Type@i }}} ==> wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Type@i }}} as sub_typ_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.


Add Parametric Morphism Γ1 Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

Lemma sub_decompose_q_typ : forall Γ S T i σ Δ Δ' τ t,
  {{Γ, S ⊢ T : Type@i}} ->
  {{Δ ⊢s σ : Γ}} ->
  {{Δ' ⊢s τ : Δ}} ->
  {{Δ' ⊢ t : S [ σ ] [ τ ]}} ->
  {{Δ' ⊢ T [ σ ∘ τ ,, t ] ≈ T [ q σ ] [ τ ,, t ] : Type@i}}.
Proof.
  intros. gen_presups.
  simpl. autorewrite with mcltt.
  rewrite wf_sub_eq_extend_compose; mauto 3;
    [| mauto
    | rewrite <- exp_eq_sub_compose_typ; mauto 4].
  eapply exp_eq_sub_cong_typ2'; [mauto 2 | mauto |].
  eapply wf_sub_eq_extend_cong; eauto.
  - rewrite wf_sub_eq_compose_assoc; mauto 3; mauto 4.
    rewrite wf_sub_eq_p_extend; eauto; mauto 4.
  - rewrite <- exp_eq_sub_compose_typ; mauto 4.
Qed.
