(* From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses. *)

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.SystemOpt Syntactic.Corollaries.
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

Theorem realize_glu_univ_elem_gen : forall A i P El,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    (forall Γ T R, {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} -> P Γ T -> glu_typ_top Γ T i A) /\
      (forall Γ t T c, glu_elem_bot Γ t T i c A -> El Γ t T d{{{ ⇑ A c }}}) /\
      (forall Γ t T a R, El Γ t T a -> {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} -> R a a -> glu_elem_top Γ t T i a A).
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
  - match_by_head glu_univ_elem invert_glu_univ_elem.
    clear_dups.
    apply_equiv_left.
    repeat split; eauto.
    repeat eexists.
    + glu_univ_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H4. trivial.
      * intros.
        saturate_weakening_escape.
        assert {{ Δ ⊢ T [σ] ≈ Type @ j[σ] : Type @ i }} by mauto 3.
        rewrite <- wf_exp_eq_typ_sub; try eassumption.
        rewrite <- H12. firstorder.
  - deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
    firstorder.
    specialize (H _ _ _ H9) as [? []].
    econstructor; eauto.
    + glu_univ_elem_econstructor; eauto.
    + apply_equiv_left. trivial.
    + mauto 2.
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H as [? [? []]]).
      progressive_invert H15.
      deepexec H20 ltac:(fun H => pose proof H).
      functional_read_rewrite_clear.
      assert {{ Δ ⊢ T [σ] ≈ Type @ j[σ] : Type @ i }} by mauto 3.
      rewrite H19.
      autorewrite with mcltt.
      trivial.

  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ℕ [ σ ]}}}; mauto 3.
  - match_by_head glu_univ_elem invert_glu_univ_elem.
    apply_equiv_left.
    repeat split; eauto.
    econstructor; trivial.

    intros.
    saturate_weakening_escape.
    assert {{ Δ ⊢ T [σ] ≈ ℕ[σ] : Type @ i }} by mauto 3.
    rewrite <- wf_exp_eq_nat_sub; try eassumption.
    rewrite <- H11. firstorder.
  - econstructor.
    + rewrite H1. mauto 3.
    + glu_univ_elem_econstructor; eauto.
    + apply_equiv_left. trivial.
    + mauto 2.
    + intros.
      saturate_weakening_escape.
      assert {{ Δ ⊢ T [σ] ≈ ℕ[σ] : Type @ i }} by mauto 3.
      rewrite H9.
      autorewrite with mcltt.
      mauto using glu_nat_readback.

  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      specialize (H12 _ _ H17).
      assert {{ Γ ⊢ IT : Type@i}} by mauto 3 using glu_univ_elem_univ_lvl, invert_sub_id.
      assert {{ Γ ⊢ IT[Id] ≈ IT : Type@i}} by mauto 3.
      rewrite H19 in H12.
      progressive_invert H16.
      destruct (H9 _ _ _ H0 H12) as [].

      transitivity {{{(Π IT OT) [σ]}}};[mauto 3 |].
      transitivity {{{Π (IT [ σ ]) (OT [q σ])}}};[mauto 3 |].
      simpl. apply wf_exp_eq_pi_cong'; [firstorder |].
      admit.

      
Admitted.
