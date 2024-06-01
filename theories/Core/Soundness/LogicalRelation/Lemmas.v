From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions Presup CtxEq Evaluation Readback PER.

From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions.
From Mcltt.Core.Soundness Require Export Weakening.Lemmas.
Import Domain_Notations.


Lemma glu_nat_per_nat : forall Γ m a,
    glu_nat Γ m a ->
    per_nat a a.
Proof.
  induction 1; mauto.
Qed.

Lemma sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A [ Id ] }}.
Proof.
  intros. gen_presups. mauto 6.
Qed.

#[export]
 Hint Resolve invert_id sub_id_typ : mcltt.

Lemma invert_sub_id : forall Γ M A,
    {{ Γ ⊢ M [ Id ] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros. remember {{{ M [ Id ]}}} as M'.
  gen M.
  induction H; intros; try congruence;
    gen_presups;
    progressive_inversion;
    mauto.
Qed.

#[export]
 Hint Resolve invert_sub_id : mcltt.

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
  destruct_all.
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
  specialize (H0 _ _ _ H2 H3).
  mauto.
Qed.


Lemma glu_nat_per_top : forall Γ m a,
    glu_nat Γ m a ->
    per_top d{{{ ⇓ ℕ a }}} d{{{ ⇓ ℕ a }}}.
Proof.
  induction 1; unfold per_top in *; intros; mauto.
  - specialize (IHglu_nat s).
    destruct_all.
    mauto.
  - specialize (H s).
    destruct_all.
    mauto.
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
  - specialize (IHglu_nat _ _ _ H1 H2).
    transitivity {{{ (succ m') [ σ ]}}}; [mauto |].
    transitivity {{{ succ m' [ σ ] }}}; mauto 6.
  - mauto.
Qed.


Lemma glu_univ_elem_univ_lvl : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ T,
      P Γ T ->
      {{ Γ ⊢ T : Type@i }}.
Proof with (simpl in *; destruct_all; gen_presups; trivial).
  induction 1 using glu_univ_elem_ind; intros.
  - apply H1 in H3...
  - apply H in H1...
  - apply H4 in H6. progressive_invert H6...
  - apply H0 in H2...
Qed.
