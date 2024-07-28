(* From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses. *)

From Coq Require Import Nat.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Syntactic Require Import CtxSub SystemOpt Corollaries CoreInversions.
From Mcltt.Core Require Import PER.
From Mcltt.Core.Semantic Require Import Realizability Readback.
From Mcltt.Core.Soundness Require Export LogicalRelation Weakening.
Import Domain_Notations.

Inductive glu_elem_bot Γ t T i c A : Prop :=
| glu_elem_bot_make : forall P El,
    {{ Γ ⊢ t : T }} ->
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    P Γ T ->
    per_bot c c ->
    (forall Δ σ w, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ w }} -> {{ Δ ⊢ t [ σ ] ≈ w : T [ σ ] }}) ->
    glu_elem_bot Γ t T i c A.
#[export]
  Hint Constructors glu_elem_bot : mcltt.


Inductive glu_elem_top Γ t T i a A : Prop :=
| glu_elem_top_make : forall P El,
    {{ Γ ⊢ t : T }} ->
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    P Γ T ->
    per_top d{{{ ⇓ A a }}} d{{{ ⇓ A a }}} ->
    (forall Δ σ w, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ A a in length Δ ↘ w }} -> {{ Δ ⊢ t [ σ ] ≈ w : T [ σ ] }}) ->
    glu_elem_top Γ t T i a A.
#[export]
  Hint Constructors glu_elem_top : mcltt.


Inductive glu_typ_top Γ T i A : Prop :=
| glu_typ_top_make :
    {{ Γ ⊢ T : Type@i }} ->
    per_top_typ A A ->
    (forall Δ σ W, {{ Δ ⊢w σ : Γ }} -> {{ Rtyp A in length Δ ↘ W }} -> {{ Δ ⊢ T [ σ ] ≈ W : Type@i }}) ->
    glu_typ_top Γ T i A.
#[export]
  Hint Constructors glu_typ_top : mcltt.

Open Scope list_scope.

Lemma wf_ctx_sub_ctx_lookup : forall n T Γ,
    {{ #n : T ∈ Γ }} ->
    forall Δ,
      {{ ⊢ Δ ⊆ Γ}} ->
      exists Δ1 T0 Δ2 T',
        Δ = Δ1 ++ T0 :: Δ2 /\
          n = length Δ1 /\
          T' = iter (S n) (fun T => {{{T [ Wk ]}}}) T0 /\
          {{ #n : T' ∈ Δ }} /\
          {{ Δ ⊢ T' ⊆ T }}.
Proof.
  induction 1; intros; progressive_inversion.
  - exists nil.
    repeat eexists; mauto 4.
  - edestruct IHctx_lookup as [Δ1 [? [? [? [? [? [? []]]]]]]]; eauto.
    exists (A0 :: Δ1). subst.
    repeat eexists; mauto 4.
Qed.


Lemma var_arith : forall Γ1 Γ2 (T : typ),
    length (Γ1 ++ T :: Γ2) - length Γ2 - 1 = length Γ1.
Proof.
  intros.
  rewrite List.app_length. simpl.
  lia.
Qed.

Lemma var_weaken_gen : forall Δ σ Γ,
    {{ Δ ⊢w σ : Γ }} ->
    forall Γ1 Γ2 T,
      Γ = Γ1 ++ T :: Γ2 ->
      {{Δ ⊢ (# (length Γ1)) [σ] ≈ # (length Δ - length Γ2 - 1) : ~(iter (S (length Γ1)) (fun T => {{{T [ Wk ]}}}) T) [ σ ] }}.
Proof.
  induction 1; intros; subst; gen_presups.
  - pose proof (app_ctx_vlookup _ _ _ _ HΔ eq_refl).
    gen_presup H0.
    clear_dups.
    apply wf_sub_id_inversion in Hτ.
    pose proof (wf_ctx_sub_length _ _ Hτ).
    transitivity {{{#(length Γ1) [Id]}}}; [mauto 3 |].
    rewrite H1, var_arith, H.
    bulky_rewrite. mauto 3.
  - pose proof (app_ctx_vlookup _ _ _ _ HΔ0 eq_refl).
    pose proof (app_ctx_lookup Γ1 T0 Γ2 _ eq_refl).
    gen_presup H2.
    clear_dups.
    assert {{ Δ', T ⊢s Wk : ~ (Γ1 ++ {{{ Γ2, T0 }}}) }} by mauto.
    transitivity {{{#(length Γ1) [Wk ∘ τ]}}}; [mauto 3 |].
    rewrite H1.
    etransitivity; [eapply wf_exp_eq_sub_compose; mauto 3 |].
    pose proof (wf_ctx_sub_length _ _ H0).

    rewrite <- exp_eq_sub_compose_typ; mauto 2.
    deepexec wf_ctx_sub_ctx_lookup ltac:(fun H => destruct H as [? [? [? [? [-> [? [-> []]]]]]]]).
    repeat rewrite List.app_length in *.
    rewrite H6 in *.
    assert (length x1 = length Γ2) by (simpl in *; lia).
    rewrite <- H9.

    etransitivity.
    + eapply wf_exp_eq_sub_cong; [ |mauto 3].
      eapply wf_exp_eq_subtyp.
      * eapply wf_exp_eq_var_weaken; [mauto 3|]; eauto.
      * mauto 4.
    + eapply wf_exp_eq_subtyp.
      * eapply IHweakening with (Γ1 := T :: _).
        reflexivity.
      * eapply wf_subtyping_subst; [ |mauto 3].
        simpl. eapply wf_subtyping_subst; mauto 3.
Qed.

Lemma var_glu_elem_bot : forall A i P El Γ T,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    P Γ T ->
    glu_elem_bot (T :: Γ) {{{#0}}} {{{T[Wk]}}} i d{{{! (length Γ)}}} A.
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 4.
  - admit.
  - intros. progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ eq_refl).
Admitted.

#[local]
 Hint Rewrite -> wf_sub_eq_extend_compose using mauto 4 : mcltt.

Theorem realize_glu_univ_elem_gen : forall A i P El,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    (forall Γ T R, {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} -> P Γ T -> glu_typ_top Γ T i A) /\
      (forall Γ t T c, {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} -> glu_elem_bot Γ t T i c A -> El Γ T t d{{{ ⇑ A c }}}) /\
      (forall Γ t T a R, {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} -> El Γ T t a -> {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} -> R a a -> glu_elem_top Γ t T i a A).
Proof.
  simpl. induction 1 using glu_univ_elem_ind.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct H as []);
    destruct_all.
  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{Type@j [ σ ]}}}; mauto 4.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    clear_dups.
    apply_equiv_left.
    repeat split; eauto.
    repeat eexists.
    + glu_univ_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H5. trivial.
      * intros.
        saturate_weakening_escape.
        rewrite <- wf_exp_eq_typ_sub; try eassumption.
        rewrite <- H5.
        firstorder.
  - deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
    firstorder.
    specialize (H _ _ _ H10) as [? []].
    econstructor; eauto.
    + apply_equiv_left. trivial.
    + mauto 2.
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H as [? [? []]]).
      progressive_invert H16.
      deepexec H20 ltac:(fun H => pose proof H).
      functional_read_rewrite_clear.
      bulky_rewrite.

  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ℕ [ σ ]}}}; mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    econstructor; trivial.

    intros.
    saturate_weakening_escape.
    assert {{ Δ ⊢ T [σ] ≈ ℕ[σ] : Type @ i }} by mauto 3.
    rewrite <- wf_exp_eq_nat_sub; try eassumption.
    rewrite <- H10. firstorder.
  - econstructor; eauto.
    + rewrite H2. mauto 3.
    + apply_equiv_left. trivial.
    + mauto 2.
    + intros.
      saturate_weakening_escape.
      bulky_rewrite.
      mauto using glu_nat_readback.

  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_weakening_escape.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      pose proof (H13 _ _ H16).
      specialize (H13 _ _ H19).
      assert {{ Γ ⊢ IT[Id] ≈ IT : Type@i}} by mauto 3.
      bulky_rewrite_in H13.
      progressive_invert H17.
      destruct (H9 _ _ _ H0 H13) as [].
      bulky_rewrite.
      simpl. apply wf_exp_eq_pi_cong'; [firstorder |].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H10 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))).
      autorewrite with mcltt in H10.
      specialize (H14 {{{Δ, IT[σ]}}} {{{σ ∘ Wk}}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)).
      specialize (H8 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      etransitivity; [| eapply H30]; mauto 3.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    destruct H10.
    econstructor; try eapply per_bot_then_per_elem; eauto.

    intros.
    saturate_weakening_escape.
    saturate_glu_info.
    match_by_head1 per_univ_elem invert_per_univ_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert {{ Δ ⊢ t [σ] : M[σ] }} by mauto 3.
    bulky_rewrite_in H24.
    econstructor; eauto.
    + eassert {{ Δ ⊢ ~ (a_sub t σ) m' : ~_ }} by (eapply wf_app'; eassumption).
      autorewrite with mcltt in H26.
      trivial.
    + mauto using domain_app_per.
    + intros.
      saturate_weakening_escape.
      progressive_invert H27.
      destruct (H15 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) equiv_b).
      handle_functional_glu_univ_elem.
      autorewrite with mcltt.

      etransitivity.
      * rewrite sub_decompose_q_typ; mauto 4.
      * simpl.
        rewrite <- sub_eq_q_sigma_id_extend; mauto 4.
        rewrite <- exp_eq_sub_compose_typ; mauto 3;
          [eapply wf_exp_eq_app_cong' |].
        -- specialize (H12 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)).
           rewrite wf_exp_eq_sub_compose with (M := t) in H12; mauto 3.
           bulky_rewrite_in H12.
        -- rewrite <- exp_eq_sub_compose_typ; mauto 3.
        -- econstructor; mauto 3.
           autorewrite with mcltt.
           rewrite <- exp_eq_sub_compose_typ; mauto 3.

  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + destruct H7. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros.
      saturate_weakening_escape.
      destruct H7. clear_dups.
      progressive_invert H14.

      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      pose proof (H20 _ _ H24).
      specialize (H20 _ _ H8).
      assert {{ Γ ⊢ IT[Id] ≈ IT : Type@i}} by mauto 3.
      bulky_rewrite_in H25.
      destruct (H11 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H29 _ _ _ H8 H9).
      rewrite H17 in *.
      autorewrite with mcltt.
      eassert {{ Δ ⊢ m[σ] : ~_ }} by (mauto 2).
      autorewrite with mcltt in H30.
      rewrite @wf_exp_eq_pi_eta' with (M := {{{m[σ]}}}); [| trivial].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; eauto.

      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H12 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ H H20)).
      autorewrite with mcltt in H12.
      specialize (H21 {{{Δ, IT[σ]}}} {{{σ ∘ Wk}}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)) as [? []].
      apply_equiv_left.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      specialize (H33 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H40 _ {{{Id}}} _ ltac:(mauto 3) ltac:(eassumption)).
      do 2 (rewrite wf_exp_eq_sub_id in H40; mauto 4).
      etransitivity; [|eassumption].
      simpl.
      assert {{ Δ, IT[σ] ⊢ # 0 : IT[σ ∘ Wk] }} by (rewrite <- exp_eq_sub_compose_typ; mauto 3).
      rewrite <- sub_eq_q_sigma_id_extend; mauto 4.
      rewrite <- exp_eq_sub_compose_typ; mauto 2.
      2:eapply sub_q; mauto 4.
      2:gen_presup H41; econstructor; mauto 3.
      eapply wf_exp_eq_app_cong'; [| mauto 3].
      symmetry.
      rewrite <- wf_exp_eq_pi_sub; mauto 4.

  - admit.

Admitted.
