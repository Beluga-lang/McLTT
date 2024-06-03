From Coq Require Import Morphisms Morphisms_Relations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Presup Syntactic.Corollaries Evaluation Readback PER.

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

Lemma glu_nat_per_top : forall Γ m a,
    glu_nat Γ m a ->
    per_top d{{{ ⇓ ℕ a }}} d{{{ ⇓ ℕ a }}}.
Proof.
  induction 1; intros s; mauto.
  - specialize (IHglu_nat s).
    destruct_conjs.
    mauto.
  - specialize (H s).
    destruct_conjs.
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
  - specialize (IHglu_nat _ _ _ H1 H5).
    transitivity {{{ (succ m') [ σ ]}}}; mauto.
    transitivity {{{ succ m' [ σ ] }}}; mauto.
  - mauto.
Qed.

Lemma glu_univ_elem_univ_lvl : forall i P El A B,
    glu_univ_elem i P El A B ->
    forall Γ T,
      P Γ T ->
      {{ Γ ⊢ T : Type@i }}.
Proof with (simpl in *; destruct_all; gen_presups; trivial).
  pose proof iff_impl_subrelation.
  assert (Proper (typ_pred_equivalence ==> pointwise_relation ctx (pointwise_relation typ iff)) id)
    by apply predicate_equivalence_pointwise.
  induction 1 using glu_univ_elem_ind; intros.
  (* Use [apply_relation_equivalence]-like tactic later *)
  - rewrite H3 in H5...
  - rewrite H1 in H3...
  - rewrite H6 in H8. dir_inversion_by_head pi_typ_pred...
  - rewrite H2 in H4...
Qed.
