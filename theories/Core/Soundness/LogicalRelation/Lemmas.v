From Coq Require Import Morphisms Morphisms_Relations.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.Corollaries.
From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions.
From Mcltt.Core.Soundness Require Export Weakening.Lemmas.
Import Domain_Notations.

Lemma pi_glu_exp_pred_pi_glu_typ_pred : forall i IR IP IEl (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}), glu_typ_pred) elem_rel OEl Γ m M a,
    {{ Γ ⊢ m : M ® a ∈ pi_glu_exp_pred i IR IP IEl elem_rel OEl }} ->
    (forall Δ m' M' b c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),
        {{ Δ ⊢ m' : M' ® b ∈ OEl _ _ equiv_c_c' }} ->
        {{ Δ ⊢ M' ® OP _ _ equiv_c_c' }}) ->
    {{ Γ ⊢ M ® pi_glu_typ_pred i IR IP IEl OP }}.
Proof.
  inversion_clear 1; econstructor; eauto.
  intros.
  edestruct H5 as [? []]; eauto.
Qed.

Lemma glu_nat_per_nat : forall Γ m a,
    glu_nat Γ m a ->
    {{ Dom a ≈ a ∈ per_nat }}.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mcltt.

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
  match_by_head (per_bot c c) ltac:(fun H => specialize (H (length Γ)) as [L []]).
  clear_dups.
  assert {{ Γ ⊢ m[Id] ≈ L : ℕ }} by mauto.
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

#[local]
 Hint Resolve glu_nat_resp_equiv : mcltt.

Lemma glu_nat_readback : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ b,
      {{ Δ ⊢w σ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Δ ↘ b }} ->
      {{ Δ ⊢ m [ σ ] ≈ b : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - transitivity {{{ zero[σ] }}}; mauto.
  - assert {{ Δ ⊢ m'[σ] ≈ M : ℕ }} by mauto.
    transitivity {{{ (succ m')[σ] }}}; mauto 3.
    transitivity {{{ succ m'[σ] }}}; mauto 4.
  - mauto.
Qed.

#[global]
  Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Lemma glu_univ_elem_univ_lvl : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T,
      {{ Γ ⊢ T ® P }} ->
      {{ Γ ⊢ T : Type@i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_typ_resp_equiv : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T T',
      {{ Γ ⊢ T ® P }} ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      {{ Γ ⊢ T' ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  split; [trivial |].
  intros.
  assert {{ Δ ⊢ T[σ] ≈ V : Type@i }}; mauto.
Qed.

Lemma glu_univ_elem_trm_resp_typ_equiv : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a T',
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      {{ Γ ⊢ t : T' ® a ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; repeat split; mauto.

  intros.
  assert {{ Δ ⊢ M[σ] ≈ V : Type@i }}; mauto.
Qed.

Lemma glu_univ_elem_typ_resp_ctx_equiv : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T Δ,
      {{ Γ ⊢ T ® P }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ T ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 2;
    econstructor; mauto.
Qed.

Lemma glu_nat_resp_wk' : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Γ ⊢ m : ℕ }} ->
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m[σ] }}} a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    transitivity {{{ zero[σ] }}}; mauto.
  - econstructor; [ |mauto].
    transitivity {{{ (succ m')[σ] }}}; mauto 4.
  - econstructor; trivial.
    intros. gen_presups.
    assert {{ Δ0 ⊢w σ ∘ σ0 : Γ }} by mauto.
    assert {{ Δ0 ⊢ m[σ ∘ σ0] ≈ v : ℕ }} by mauto 4.
    transitivity {{{ m[σ ∘ σ0] }}}; mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m[σ] }}} a.
Proof.
  mauto using glu_nat_resp_wk'.
Qed.
#[export]
 Hint Resolve glu_nat_resp_wk : mcltt.

Lemma glu_univ_elem_trm_escape : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ t : T }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  match_by_head (per_bot c c) ltac:(fun H => specialize (H (length Γ)) as [Lc []]).
  match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [Lb []]).
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  clear_dups.
  assert {{ Γ ⊢ m[Id] ≈ Lc : M[Id] }} by mauto.
  gen_presups.
  mauto.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Dom A ≈ B ∈ per_univ i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros; eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
Qed.

Lemma glu_univ_elem_per_elem : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a R,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ DF A ≈ B ∈ per_univ_elem i ↘ R }} ->
      {{ Dom a ≈ a ∈ R }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    try do 2 match_by_head1 per_univ_elem invert_per_univ_elem;
    simpl_glu_rel;
    try fold (per_univ j' a a);
    mauto 4 using glu_univ_elem_per_univ.

  intros.
  destruct_rel_mod_app.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  do_per_univ_elem_irrel_assert.

  econstructor; firstorder eauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  intros.
  destruct_rel_mod_eval.
  edestruct H11 as [? []]; eauto.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T : Type@i }}.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [| eapply glu_univ_elem_trm_typ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_equiv : forall i P El A B,
    {{ Glu A ≈ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a t',
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ t ≈ t' : T }} ->
      {{ Γ ⊢ t' : T ® a ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_equiv; mauto.

  - econstructor; eauto.
    invert_per_univ_elem H3.
    intros.
    destruct_rel_mod_eval.
    assert {{ Δ ⊢ m' : IT [σ]}} by eauto using glu_univ_elem_trm_escape.
    edestruct H12 as [? []]; eauto.
    eexists; split; eauto.
    enough {{ Δ ⊢ m[σ] m' ≈ t'[σ] m' : OT[σ,,m'] }} by eauto.
    assert {{ Γ ⊢ m ≈ t' : Π IT OT }} as Hty by mauto.
    eassert {{ Δ ⊢ IT[σ] : Type@_ }} by mauto 3.
    eapply wf_exp_eq_sub_cong with (Γ := Δ) in Hty; [| eapply sub_eq_refl; mauto 3].
    autorewrite with mcltt in Hty.
    eapply wf_exp_eq_app_cong with (N := m') (N' := m') in Hty; try pi_univ_level_tac; [|mauto 2].
    autorewrite with mcltt in Hty.
    eassumption.
  - intros.
    assert {{ Δ ⊢ m[σ] ≈ t'[σ] : M[σ] }} by mauto 4.
    mauto 4.
Qed.
