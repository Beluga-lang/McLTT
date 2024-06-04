From Coq Require Import Morphisms Morphisms_Relations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation PER Presup CtxEq Readback Syntactic.Corollaries System.Lemmas.

From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions.
From Mcltt.Core.Soundness Require Export Weakening.Lemmas.
Import Domain_Notations.

Lemma glu_nat_per_nat : forall Γ m a,
    glu_nat Γ m a ->
    per_nat a a.
Proof.
  induction 1; mauto.
Qed.

Lemma glu_nat_escape : forall Γ m a,
    glu_nat Γ m a ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ m : ℕ }}.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  specialize (H (length Γ)).
  destruct_conjs.
  specialize (H0 _ _ _ H2 H3).
  gen_presups.
  mauto.
Qed.

#[export]
Hint Resolve glu_nat_escape : mcltt.

Lemma glu_nat_resp_equiv : forall Γ m a,
    glu_nat Γ m a ->
    forall m',
    {{ Γ ⊢ m ≈ m' : ℕ }} ->
    glu_nat Γ m' a.
Proof.
  induction 1; intros; mauto.
  econstructor; trivial.
  intros.
  transitivity {{{ m[σ] }}}; mauto.
Qed.


Lemma glu_nat_readback : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ b,
      {{ Δ ⊢w σ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Δ ↘ b }} ->
      {{ Δ ⊢ m [ σ ] ≈ b : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - transitivity {{{ zero [ σ ] }}}; mauto.
  - specialize (IHglu_nat _ _ _ H1 H5).
    transitivity {{{ (succ m') [ σ ]}}}; mauto.
    transitivity {{{ succ m' [ σ ] }}}; mauto.
  - mauto.
Qed.

#[global]
  Ltac simpl_glu_rel :=
  repeat simpl_glu_rel1;
  repeat invert_glu_rel1;
  destruct_all;
  gen_presups.


Lemma glu_univ_elem_univ_lvl : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ T,
      P Γ T ->
      {{ Γ ⊢ T : Type@i }}.
Proof.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.


Lemma glu_univ_elem_typ_resp_equiv : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ T T',
      P Γ T ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      P Γ T'.
Proof.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto.

  split; [trivial |].
  intros.
  specialize (H4 _ _ _ H2 H5); mauto.
Qed.


Lemma glu_univ_elem_trm_resp_typ_equiv : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ t T a T',
      El Γ t T a ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      El Γ t T' a.
Proof.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; repeat split; mauto.
  
  intros.
  specialize (H3 _ _ _ H2 H7); mauto.
Qed.


Lemma glu_univ_elem_typ_resp_ctx_equiv : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ T Δ,
      P Γ T ->
      {{ ⊢ Γ ≈ Δ }} ->
      P Δ T.
Proof.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 2.

  - econstructor; mauto.

  - mauto 6.
Qed.


Lemma glu_nat_resp_wk' : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Γ ⊢ m : ℕ }} ->
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m [ σ ]}}} a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    transitivity {{{ zero [ σ ]}}}; mauto.
  - econstructor; [ |mauto].
    transitivity {{{ (succ m') [σ]}}}; mauto 4.
  - econstructor; trivial.
    intros. gen_presups.
    assert {{ Δ0 ⊢w σ ∘ σ0 : Γ }} by mauto.
    specialize (H0 _ _ _ H5 H4).
    transitivity {{{ m [ σ ∘ σ0 ]}}}; mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m [ σ ]}}} a.
Proof.
  mauto using glu_nat_resp_wk'.
Qed.
