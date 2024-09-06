From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.Corollaries.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import NbE Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation.Core Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Add Parametric Morphism i a Γ A M : (glu_elem_bot i a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Add Parametric Morphism i a Γ A M R (H : per_univ_elem i R a a) : (glu_elem_top i a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    pose proof (per_elem_then_per_top H Hmm') as Hmm'';
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm'' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Lemma glu_univ_elem_typ_unique_upto_exp_eq : forall {i j a P P' El El' Γ A A'},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max i j) }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A ® glu_typ_top i a }} as [] by mauto 3.
  assert {{ Γ ⊢ A' ® glu_typ_top j a }} as [] by mauto 3.
  match_by_head per_top_typ ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert {{ Γ ⊢ A : Type@(max i j) }} by mauto 4 using lift_exp_max_left.
  assert {{ Γ ⊢ A' : Type@(max i j) }} by mauto 4 using lift_exp_max_right.
  assert {{ Γ ⊢ A[Id] ≈ V : Type@i }} by mauto 4.
  assert {{ Γ ⊢ A[Id] ≈ V : Type@(max i j) }} by mauto 4 using lift_exp_eq_max_left.
  assert {{ Γ ⊢ A'[Id] ≈ V : Type@j }} by mauto 4.
  assert {{ Γ ⊢ A'[Id] ≈ V : Type@(max i j) }} by mauto 4 using lift_exp_eq_max_right.
  autorewrite with mcltt in *...
Qed.

#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq : mcltt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq_ge : forall {i j a P P' El El' Γ A A'},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof with mautosolve 4.
  intros.
  replace j with (max i j) by lia...
Qed.

#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq_ge : mcltt.

Lemma glu_univ_elem_typ_unique_upto_exp_eq' : forall {i a P El Γ A A'},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_univ_elem_typ_unique_upto_exp_eq' : mcltt.

Lemma glu_univ_elem_per_univ_elem_typ_escape : forall {i a a' elem_rel P P' El El' Γ A A'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ elem_rel }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof with mautosolve 4.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} by (setoid_rewrite Hper; eassumption).
  handle_functional_glu_univ_elem...
Qed.

#[export]
Hint Resolve glu_univ_elem_per_univ_elem_typ_escape : mcltt.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof.
  intros * [] **...
  mauto 4.
Qed.

#[export]
Hint Resolve glu_univ_elem_per_univ_typ_escape : mcltt.

Lemma glu_univ_elem_per_univ_typ_iff : forall {i a a' P P' El El'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  intros * Hper **.
  eapply functional_glu_univ_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.

Corollary glu_univ_elem_cumu_ge : forall {i j a P El},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    exists P' El', {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }}.
Proof.
  intros.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [R] by mauto.
  assert {{ DF a ≈ a ∈ per_univ_elem j ↘ R }} by mauto.
  mauto.
Qed.

#[export]
Hint Resolve glu_univ_elem_cumu_ge : mcltt.

Corollary glu_univ_elem_cumu_max_left : forall {i j a P El},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    exists P' El', {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }}.
Proof.
  intros.
  assert (i <= max i j) by lia.
  mauto.
Qed.

Corollary glu_univ_elem_cumu_max_right : forall {i j a P El},
    {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} ->
    exists P' El', {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }}.
Proof.
  intros.
  assert (j <= max i j) by lia.
  mauto.
Qed.

Section glu_univ_elem_cumulativity.
  #[local]
  Lemma glu_univ_elem_cumulativity_ge : forall {i j a P P' El El'},
      i <= j ->
      {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
      {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
      (forall Γ A, {{ Γ ⊢ A ® P }} -> {{ Γ ⊢ A ® P' }}) /\
        (forall Γ A M m, {{ Γ ⊢ M : A ® m ∈ El }} -> {{ Γ ⊢ M : A ® m ∈ El' }}) /\
        (forall Γ A M m, {{ Γ ⊢ A ® P }} -> {{ Γ ⊢ M : A ® m ∈ El' }} -> {{ Γ ⊢ M : A ® m ∈ El }}).
  Proof with mautosolve 4.
    simpl.
    intros * Hge Hglu Hglu'. gen El' P' j.
    induction Hglu using glu_univ_elem_ind; repeat split; intros;
      try assert {{ DF a ≈ a ∈ per_univ_elem j ↘ in_rel }} by mauto 2;
      invert_glu_univ_elem Hglu';
      handle_functional_glu_univ_elem;
      simpl in *;
      try solve [repeat split; intros; destruct_conjs; mauto 2 | intuition mauto 3].

    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      econstructor; intros; mauto 4.
      + assert {{ Δ ⊢ IT[σ] ® IP }} by mauto.
        enough (forall Γ A, {{ Γ ⊢ A ® IP }} -> {{ Γ ⊢ A ® IP' }}) by mauto 4.
        eapply proj1...
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        assert (forall Γ A, {{ Γ ⊢ A ® OP m equiv_m }} -> {{ Γ ⊢ A ® OP' m equiv_m }}) by (eapply proj1; mauto).
        enough {{ Δ ⊢ OT[σ,,M] ® OP m equiv_m }} by mauto.
        enough {{ Δ ⊢ M : IT[σ] ® m ∈ IEl }} by mauto.
        eapply IHHglu...
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto 4.
      + enough (forall Γ A, {{ Γ ⊢ A ® IP }} -> {{ Γ ⊢ A ® IP' }}) by mauto 4.
        eapply proj1...
      + match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct_rel_mod_app.
        handle_per_univ_elem_irrel.
        eexists; split; mauto 4.
        assert (forall Γ A M m, {{ Γ ⊢ M : A ® m ∈ OEl n equiv_n }} -> {{ Γ ⊢ M : A ® m ∈ OEl' n equiv_n }}) by (eapply proj1, proj2; mauto 4).
        enough {{ Δ ⊢ M[σ] N : OT[σ,,N] ® fa ∈ OEl n equiv_n }} by mauto 4.
        assert {{ Δ ⊢ N : IT[σ] ® n ∈ IEl }} by (eapply IHHglu; mauto 3).
        assert (exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl n equiv_n }}) by mauto 4.
        destruct_conjs.
        functional_eval_rewrite_clear...
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      handle_per_univ_elem_irrel.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      handle_per_univ_elem_irrel.
      match goal with
      | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ~?a }} |- _ =>
          rename a into b
      end.
      eexists; split; mauto 4.
      assert (forall Γ A M m, {{ Γ ⊢ A ® OP n equiv_n }} -> {{ Γ ⊢ M : A ® m ∈ OEl' n equiv_n }} -> {{ Γ ⊢ M : A ® m ∈ OEl n equiv_n }}) by (eapply proj2, proj2; eauto 3).
      assert {{ Δ ⊢ OT[σ,,N] ® OP n equiv_n }} by mauto 4.
      enough {{ Δ ⊢ M[σ] N : OT[σ,,N] ® fa ∈ OEl' n equiv_n }} by mauto 4.
      assert {{ Δ ⊢ N : IT[σ] ® n ∈ IEl' }} by (eapply IHHglu; mauto 3).
      assert {{ Δ ⊢ IT[σ] ® IP' }} by (eapply glu_univ_elem_trm_typ; mauto 2).
      assert {{ Δ ⊢ IT0[σ] ® IP' }} by mauto 2.
      assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Type@j }} as HITeq by mauto 2.
      assert {{ Δ ⊢ N : IT0[σ] ® n ∈ IEl' }} by (rewrite <- HITeq; mauto 3).
      assert (exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ] N : OT0[σ,,N] ® mn ∈ OEl' n equiv_n }}) by mauto 3.
      destruct_conjs.
      functional_eval_rewrite_clear.
      assert {{ DG b ∈ glu_univ_elem j ↘ OP' n equiv_n ↘ OEl' n equiv_n }} by mauto 3.
      assert {{ Δ ⊢ OT0[σ,,N] ® OP' n equiv_n }} by (eapply glu_univ_elem_trm_typ; mauto 3).
      enough {{ Δ ⊢ OT[σ,,N] ≈ OT0[σ,,N] : Type@j }} as ->...
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
      destruct_by_head neut_glu_typ_pred.
      econstructor...
    - destruct_by_head neut_glu_exp_pred.
      econstructor...
  Qed.
End glu_univ_elem_cumulativity.

Corollary glu_univ_elem_typ_cumu_ge : forall {i j a P P' El El' Γ A},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A ® P' }}.
Proof.
  intros.
  eapply glu_univ_elem_cumulativity_ge; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_left : forall {i j a P P' El El' Γ A},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A ® P' }}.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_typ_cumu_max_right : forall {i j a P P' El El' Γ A},
    {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A ® P' }}.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_typ_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_ge : forall {i j a P P' El El' Γ A M m},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_left : forall {i j a P P' El El' Γ A M m},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_cumu_max_right : forall {i j a P P' El El' Γ A M m},
    {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower :  forall {i j a P P' El El' Γ A M m},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }}.
Proof.
  intros * ? ? ?. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_ge; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_left :  forall {i j a P P' El El' Γ A M m},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }}.
Proof.
  intros.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

Corollary glu_univ_elem_exp_lower_max_right :  forall {i j a P P' El El' Γ A M m},
    {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }}.
Proof.
  intros.
  assert (j <= max i j) by lia.
  eapply glu_univ_elem_exp_lower; mauto 4.
Qed.

Lemma glu_univ_elem_exp_conv : forall {i j k a a' P P' El El' Γ A M m},
    {{ Dom a ≈ a' ∈ per_univ k }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ A ® P' }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros * [] ? ? ? ?.
  assert {{ Dom a ≈ a' ∈ per_univ (max i k) }} as Haa' by (eexists; mauto using per_univ_elem_cumu_max_right).
  assert (exists P El, {{ DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El }}) as [Pik [Elik]] by mauto using glu_univ_elem_cumu_max_left.
  assert {{ DG a' ∈ glu_univ_elem (max i k) ↘ Pik ↘ Elik }} by (setoid_rewrite <- Haa'; eassumption).
  assert {{ Γ ⊢ M : A ® m ∈ Elik }} by (eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption).
  assert (exists P El, {{ DG a' ∈ glu_univ_elem (max j (max i k)) ↘ P ↘ El }}) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_max_right.
  assert {{ Γ ⊢ M : A ® m ∈ Eltop }} by (eapply glu_univ_elem_exp_cumu_max_right; [| | eassumption]; eassumption).
  eapply glu_univ_elem_exp_lower_max_left; mauto.
Qed.

Lemma glu_univ_elem_per_subtyp_typ_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ⊆ A' }}.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  gen A' A Γ. gen El' El P' P.
  induction Hsubtyp using per_subtyp_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    destruct_by_head pi_glu_typ_pred;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    try solve [simpl in *; mauto 3].
  - match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert {{ Γ ⊢ A[Id] ≈ A : Type@i }} as <- by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ A' : Type@i }} as <- by mauto 3.
    assert {{ Γ ⊢ A'[Id] ≈ V : Type@i }} as -> by mauto 4.
    eapply wf_subtyp_refl'.
    mauto 4.
  - bulky_rewrite.
    mauto 3.
  - destruct_by_head pi_glu_typ_pred.
    rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl.
    rename A0 into A'. rename IT0 into IT'. rename OT0 into OT'.
    rename x3 into OP'. rename x4 into OEl'.
    assert {{ Γ ⊢ IT ® IP }}.
    {
      assert {{ Γ ⊢ IT[Id] ® IP }} by mauto 4.
      simpl in *.
      autorewrite with mcltt in *; mauto 3.
    }
    assert {{ Γ ⊢ IT' ® IP }}.
    {
      assert {{ Γ ⊢ IT'[Id] ® IP }} by mauto 4.
      simpl in *.
      autorewrite with mcltt in *; mauto 3.
    }
    do 2 bulky_rewrite1.
    assert {{ Γ ⊢ IT ≈ IT' : Type@i }} by mauto 4.
    enough {{ Γ, IT' ⊢ OT ⊆ OT' }} by mauto 3.
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len_len' by (eapply per_bot_then_per_elem; mauto 4).
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel }} as equiv_len_len by (eapply per_bot_then_per_elem; mauto 4).
    assert {{ Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto 4).
    handle_per_univ_elem_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    apply_relation_equivalence.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ ⇑! a (length Γ) ↘ ~?a0 }},
        _: {{ ⟦ B' ⟧ ρ' ↦ ⇑! a' (length Γ) ↘ ~?a0' }} |- _ =>
        rename a0 into b;
        rename a0' into b'
    end.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP d{{{ ⇑! a (length Γ) }}} equiv_len_len ↘ OEl d{{{ ⇑! a (length Γ) }}} equiv_len_len }} by mauto 4.
    assert {{ DG b' ∈ glu_univ_elem i ↘ OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' ↘ OEl' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }} by mauto 4.
    assert {{ Γ, IT' ⊢ OT ® OP d{{{ ⇑! a (length Γ) }}} equiv_len_len }}.
    {
      assert {{ Γ, IT ⊢ #0 : IT[Wk] ® ⇑! a (length Γ) ∈ IEl }} by (eapply var0_glu_elem; mauto 3).
      assert {{ ⊢ Γ, IT' ≈ Γ, IT }} as -> by mauto.
      assert {{ Γ, IT ⊢ OT[Wk,,#0] ≈ OT : Type@i }} as <- by (bulky_rewrite1; mauto 2).
      mauto 4.
    }
    assert {{ Γ, IT' ⊢ OT' ® OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }}.
    {
      assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® ⇑! a' (length Γ) ∈ IEl }} by (eapply var0_glu_elem; mauto 3).
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ® OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }} by mauto 4.
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ≈ OT' : Type@i }} as <- by (bulky_rewrite1; mauto 2).
      mauto 4.
    }
    mauto 3.
Qed.

#[export]
Hint Resolve glu_univ_elem_per_subtyp_typ_escape : mcltt.

Lemma glu_univ_elem_per_subtyp_trm_if : forall {i a a' P P' El El' Γ A A' M m},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A' ® m ∈ El' }}.
Proof.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  assert {{ Γ ⊢ A ⊆ A' }} by (eapply glu_univ_elem_per_subtyp_typ_escape; only 4: eapply glu_univ_elem_trm_typ; mauto).
  gen m M A' A. gen Γ. gen El' El P' P.
  induction Hsubtyp using per_subtyp_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    repeat invert_glu_rel1;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    repeat invert_glu_rel1;
    try solve [simpl in *; intuition mauto 3].
  - match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Γ)) as [V []]).
    econstructor; mauto 3.
    + econstructor; mauto 3.
    + intros.
      match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Δ)) as [? []]).
      functional_read_rewrite_clear.
      assert {{ Δ ⊢ A[σ] ⊆ A'[σ] }} by mauto 3.
      assert {{ Δ ⊢ M[σ] ≈ M' : A[σ] }} by mauto 3.
      mauto 3.
  - simpl in *.
    destruct_conjs.
    intuition mauto 3.
    assert (exists P El, {{ DG m ∈ glu_univ_elem j ↘ P ↘ El }}) as [? [?]] by mauto 3.
    do 2 eexists; split; mauto 3.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mautosolve 3.
  - rename A0 into A'.
    rename IT0 into IT'. rename OT0 into OT'.
    rename x into IP. rename x0 into IEl.
    rename x1 into OP. rename x2 into OEl.
    rename x3 into OP'. rename x4 into OEl'.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
    + enough {{ Sub Π a ρ B <: Π a' ρ' B' at i }} by (eapply per_elem_subtyping; try eassumption).
      econstructor; mauto 3.
    + intros.
      assert {{ Γ ⊢w Id : Γ }} by mauto 3.
      assert {{ Γ ⊢ IT ® IP }}.
      {
        assert {{ Γ ⊢ IT[Id] ® IP }} by mauto 3.
        simpl in *.
        autorewrite with mcltt in *; mauto 3.
      }
      assert {{ Γ ⊢ IT' ® IP }}.
      {
        assert {{ Γ ⊢ IT'[Id] ® IP }} by mauto 3.
        simpl in *.
        autorewrite with mcltt in *; mauto 3.
      }
      assert {{ Δ ⊢ IT'[σ] ≈ IT[σ] : Type@i }} by (symmetry; mauto 4 using glu_univ_elem_per_univ_typ_escape).
      assert {{ Δ ⊢ N : IT'[σ] ® n ∈ IEl }} by (simpl; bulky_rewrite1; eassumption).
      assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{Δ ⊢ M[σ] N : OT'[σ,,N] ® mn ∈ OEl n equiv_n }}) by mauto 3.
      destruct_conjs.
      eexists; split; mauto 3.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      match goal with
      | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ~?a }},
          _: {{ ⟦ B' ⟧ ρ' ↦ n ↘ ~?a' }} |- _ =>
          rename a into b;
          rename a' into b'
      end.
      assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
      assert {{ DG b' ∈ glu_univ_elem i ↘ OP' n equiv_n ↘ OEl' n equiv_n }} by mauto 3.
      assert {{ Δ ⊢ OT'[σ,,N] ® OP n equiv_n }} by (eapply glu_univ_elem_trm_typ; mauto 3).
      assert {{ Sub b <: b' at i }} by mauto 3.
      assert {{ Δ ⊢ OT'[σ,,N] ⊆ OT[σ,,N] }} by mauto 3.
      intuition.
Qed.

Lemma glu_univ_elem_per_subtyp_trm_conv : forall {i j k a a' P P' El El' Γ A A' M m},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem k ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A' ® m ∈ El' }}.
Proof.
  intros.
  assert {{ Sub a <: a' at (max i (max j k)) }} by mauto using per_subtyp_cumu_left.
  assert (j <= max i (max j k)) by lia.
  assert (exists P El, {{ DG a ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El }}) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_ge.
  assert (k <= max i (max j k)) by lia.
  assert (exists P El, {{ DG a' ∈ glu_univ_elem (max i (max j k)) ↘ P ↘ El }}) as [Ptop' [Eltop']] by mauto using glu_univ_elem_cumu_ge.
  assert {{ Γ ⊢ A' ® Ptop' }} by (eapply glu_univ_elem_typ_cumu_ge; mauto).
  assert {{ Γ ⊢ M : A ® m ∈ Eltop }} by (eapply @glu_univ_elem_exp_cumu_ge with (i := j); mauto).
  assert {{ Γ ⊢ M : A' ® m ∈ Eltop' }} by (eapply glu_univ_elem_per_subtyp_trm_if; mauto).
  eapply glu_univ_elem_exp_lower; mauto.
Qed.

(** Lemmas for [glu_rel_typ_with_sub] and [glu_rel_exp_with_sub] *)

Lemma mk_glu_rel_typ_with_sub' : forall {i Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    (exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}) ->
    (forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ A[σ] ® P }}) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub' : mcltt.

Lemma mk_glu_rel_typ_with_sub'' : forall {i Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Dom a ≈ a ∈ per_univ i }} ->
    (forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ A[σ] ® P }}) ->
    glu_rel_typ_with_sub i Δ A σ ρ.
Proof.
  intros * ? [] ?.
  assert (exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}) as [? []] by mauto.
  eapply mk_glu_rel_typ_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub'' : mcltt.

Lemma mk_glu_rel_exp_with_sub' : forall {i Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    (exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}) ->
    (forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub' : mcltt.

Lemma mk_glu_rel_exp_with_sub'' : forall {i Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    {{ Dom a ≈ a ∈ per_univ i }} ->
    (forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}) ->
    glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? ? [] ?.
  assert (exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}) as [? []] by mauto.
  eapply mk_glu_rel_exp_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub'' : mcltt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : forall {i Δ A M σ Γ ρ},
  {{ Δ ⊢s σ : Γ }} ->
  glu_rel_exp_with_sub i Δ M A σ ρ ->
  glu_rel_exp_with_sub (S i) Δ A {{{ Type@i }}} σ ρ.
Proof.
  intros * ? [].
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Type@i }} by mauto using glu_univ_elem_trm_univ_lvl.
  repeat split; try do 2 eexists; mauto 3.
  split; mauto 4.
  eapply glu_univ_elem_trm_typ; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mcltt.

Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : forall {i Δ A j σ ρ},
  glu_rel_exp_with_sub i Δ A {{{ Type@j }}} σ ρ ->
  glu_rel_typ_with_sub j Δ A σ ρ.
Proof.
  intros * [].
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mcltt.

Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : forall {Δ A j σ Γ ρ},
  {{ Δ ⊢s σ : Γ }} ->
  glu_rel_typ_with_sub j Δ A σ ρ ->
  glu_rel_exp_with_sub (S j) Δ A {{{ Type@j }}} σ ρ.
Proof.
  intros * ? [].
  simplify_evals.
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Type@j }} by mauto 4 using glu_univ_elem_univ_lvl.
  repeat split; try do 2 eexists; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mcltt.

(** Lemmas for [glu_ctx_env] *)

Lemma glu_ctx_env_sub_resp_ctx_eq : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    forall {Δ Δ' σ ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Δ' ⊢s σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hctxeq;
    apply_predicate_equivalence;
    simpl in *;
    mauto 4.

  destruct_by_head cons_glu_sub_pred.
  econstructor; mauto 4.
  rewrite <- Hctxeq; eassumption.
Qed.

Add Parametric Morphism Sb Γ (H : glu_ctx_env Sb Γ) : Sb
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  intros.
  split; intros; eapply glu_ctx_env_sub_resp_ctx_eq; mauto.
Qed.

Lemma glu_ctx_env_sub_resp_sub_eq : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    forall {Δ σ σ' ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ ≈ σ' : Γ }} ->
      {{ Δ ⊢s σ' ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hsubeq;
    apply_predicate_equivalence;
    simpl in *;
    gen_presup Hsubeq;
    try eassumption.
  
  destruct_by_head cons_glu_sub_pred.
  econstructor; mauto 4.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Type@i }} as <- by mauto 3.
  assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 3.
  eassumption.
Qed.

Add Parametric Morphism Sb Γ (H : glu_ctx_env Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq : forall {i Γ A Sb Δ σ σ' ρ},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ ≈ σ' : Γ, A }} ->
    {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred i Γ A Sb }} ->
    {{ Δ ⊢s σ' ® ρ ∈ cons_glu_sub_pred i Γ A Sb }}.
Proof.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  gen_presup Heq.
  assert {{ Δ ⊢s Wk∘σ : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ' : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} by mauto 3.
  econstructor; mauto 3.
  - assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Type@i }} as <- by mauto 4.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <-; mauto 3.
  - assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} as <-; eassumption.
Qed.

Add Parametric Morphism i Γ A Sb Δ (Hglu : {{ EG Γ ∈ glu_ctx_env ↘ Sb }}) (HA : {{ Γ ⊢ A : Type@i }}) : (cons_glu_sub_pred i Γ A Sb Δ)
    with signature wf_sub_eq Δ {{{ Γ, A }}} ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq.
Qed.

Lemma glu_ctx_env_per_env : forall {Γ Sb env_rel Δ σ ρ},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Dom ρ ≈ ρ ∈ env_rel }}.
Proof.
  intros * Hglu Hper.
  gen ρ σ Δ env_rel.
  induction Hglu; intros;
    invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto 3.

  rename i0 into j.
  inversion_clear_by_head cons_glu_sub_pred.
  assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }} by intuition.
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  assert (exists P' El', {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }}) as [? []] by mauto 3 using glu_univ_elem_cumu_max_left.
  eexists; eapply glu_univ_elem_per_elem; mauto using per_univ_elem_cumu_max_right.
  eapply glu_univ_elem_exp_cumu_max_left; [| | eassumption]; eassumption.
Qed.

Lemma glu_ctx_env_wf_ctx : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; intros; mauto.
Qed.

Lemma glu_ctx_env_sub_escape : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ : Γ }}.
Proof.
  induction 1; intros;
    handle_functional_glu_univ_elem;
    destruct_by_head cons_glu_sub_pred;
    eassumption.
Qed.

#[export]
Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mcltt.

Lemma glu_ctx_env_per_ctx_env : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}.
Proof.
  intros.
  enough {{ ⊨ Γ }} by eassumption.
  mauto using completeness_fundamental_ctx.
Qed.

#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mcltt.

Lemma glu_ctx_env_resp_per_ctx_helper : forall {Γ Γ' Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env ↘ Sb' }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    (Sb -∙> Sb').
Proof.
  intros * Hglu Hglu' HΓΓ'.
  gen Sb' Γ'.
  induction Hglu; intros;
    destruct (completeness_fundamental_ctx_eq _ _ HΓΓ') as [env_relΓ Hper];
    apply_predicate_equivalence;
    handle_per_univ_elem_irrel;
    dependent destruction Hglu';
    apply_predicate_equivalence;
    invert_per_ctx_env Hper;
    handle_per_ctx_env_irrel;
    gintuition.

  rename i0 into j.
  rename Γ0 into Γ'.
  rename A0 into A'.
  rename TSb0 into TSb'.
  rename i1 into k.
  inversion HΓΓ' as [|? ? l]; subst.
  assert (TSb -∙> TSb') by intuition.
  intros Δ σ ρ [].
  saturate_refl_for per_ctx_env.
  assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }}
    by (eapply glu_ctx_env_per_env; [| | eassumption]; eassumption).
  assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
  assert (glu_rel_typ_with_sub j Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) as [] by mauto 3.
  destruct_rel_typ.
  handle_functional_glu_univ_elem.
  rename a0 into a'.
  rename El0 into El'.
  rename P0 into P'.
  econstructor; mauto 4.
  assert (exists Pmax Elmax, {{ DG a ∈ glu_univ_elem (max i l) ↘ Pmax ↘ Elmax }}) as [Pmax [Elmax]]
      by mauto using glu_univ_elem_cumu_max_left.
  assert (i <= max i l) by lia.
  assert {{ Δ0 ⊢ #0[σ0] : A'[Wk][σ0] ® ~(ρ0 0) ∈ Elmax }}.
  {
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk][σ0] : Type@l }} by mauto 3.
    assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk][σ0] : Type@(max i l) }} as <- by mauto 2 using lift_exp_eq_max_right.
    eapply glu_univ_elem_exp_cumu_ge; mauto 3.
  }
  eapply glu_univ_elem_exp_conv; [eexists | | | |]; intuition.
  autorewrite with mcltt.
  eassumption.
Qed.

Corollary functional_glu_ctx_env : forall {Γ Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EG Γ ∈ glu_ctx_env ↘ Sb' }} ->
    (Sb <∙> Sb').
Proof.
  intros.
  assert {{ ⊢ Γ ≈ Γ }} by mauto using glu_ctx_env_wf_ctx.
  split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.

Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ EG ~?Γ ∈ glu_ctx_env ↘ ?Sb1 }},
      H2 : {{ EG ~?Γ ∈ glu_ctx_env ↘ ?Sb2 }} |- _ =>
      assert_fails (unify Sb1 Sb2);
      match goal with
      | H : Sb1 <∙> Sb2 |- _ => fail 1
      | _ => assert (Sb1 <∙> Sb2) by (eapply functional_glu_ctx_env; [apply H1 | apply H2]) || tactic_error Sb1 Sb2
      end
  end.

Ltac apply_functional_glu_ctx_env :=
  repeat apply_functional_glu_ctx_env1.

Ltac handle_functional_glu_ctx_env :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_ctx_env;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_ctx_env_cons_clean_inversion : forall {Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env ↘ TSb }} ->
  {{ EG Γ, A ∈ glu_ctx_env ↘ Sb }} ->
  exists i,
    {{ Γ ⊢ A : Type@i }} /\
      (forall Δ σ ρ,
          {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
          glu_rel_typ_with_sub i Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred i Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head glu_ctx_env progressive_invert.
  apply_functional_glu_ctx_env.
  eexists; intuition.
  assert (Sb <∙> cons_glu_sub_pred i Γ A TSb0) as -> by eassumption.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + (inversion H; subst).

Lemma glu_ctx_env_subtyp_sub_if : forall Γ Γ' Sb Sb' Δ σ ρ,
    {{ ⊢ Γ ⊆ Γ' }} ->
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env ↘ Sb' }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb' }}.
Proof.
  intros * Hsubtyp Hglu Hglu'.
  gen ρ σ Δ. gen Sb' Sb.
  induction Hsubtyp; intros;
    invert_glu_ctx_env Hglu;
    invert_glu_ctx_env Hglu';
    handle_functional_glu_ctx_env;
    eauto.

  rename Δ into Γ'.
  rename i0 into j.
  rename i1 into k.
  rename TSb0 into TSb'.
  destruct_by_head cons_glu_sub_pred.
  assert (glu_rel_typ_with_sub k Δ A' {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) as [] by intuition.
  rename a0 into a'.
  rename P0 into P'.
  rename El0 into El'.
  assert (exists tail_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ tail_rel }}) as [tail_rel] by mauto 3 using glu_ctx_env_per_ctx_env.
  assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  assert {{ ⊢ Γ, A ⊆ Γ', A' }} by mauto 3.
  econstructor; mauto; intuition.
  assert {{ Γ ⊨ A ⊆ A' }} as [] by mauto 3 using completeness_fundamental_subtyp.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption tail_rel).
  destruct_by_head rel_exp.
  handle_functional_glu_ctx_env.
  eapply glu_univ_elem_per_subtyp_trm_conv; mauto 3.
  autorewrite with mcltt.
  eassumption.
Qed.

Lemma glu_ctx_env_sub_monotone : forall Γ Sb,
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    forall Δ' σ Δ τ ρ,
      {{ Δ ⊢s τ ® ρ ∈ Sb }} ->
      {{ Δ' ⊢w σ : Δ }} ->
      {{ Δ' ⊢s τ ∘ σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hσ;
    apply_predicate_equivalence;
    simpl in *;
    mauto 3.

  destruct_by_head cons_glu_sub_pred.
  econstructor; mauto 3.
  - assert {{ Δ' ⊢ #0[σ0][σ] : A[Wk][σ0][σ] ® ~(ρ 0) ∈ El }} by (eapply glu_univ_elem_exp_monotone; mauto 3).
    assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢ #0[σ0∘σ] ≈ #0[σ0][σ] : A[Wk][σ0∘σ] }} as -> by mauto 3.
    assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Δ' ⊢ A[Wk][σ0][σ] ≈ A[Wk][σ0∘σ] : Type@i }} as <- by mauto 3.
    eassumption.
  - assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢s (Wk ∘ σ0) ∘ σ ≈ Wk ∘ (σ0 ∘ σ) : Γ }} as <- by mauto 3.
    mauto 3.
Qed.

Lemma cons_glu_sub_pred_helper : forall {Γ Sb Δ σ ρ A a i P El M c},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Δ ⊢ M : A[σ] ® c ∈ El }} ->
    {{ Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb }}.
Proof.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ M : A[σ] }} by mauto 2 using glu_univ_elem_trm_escape.
  assert {{ Δ ⊢s σ,,M : Γ, A }} by mauto 2.
  econstructor; mauto 3;
    autorewrite with mcltt; mauto 3.

  assert {{ Δ ⊢ #0[σ,,M] ≈ M : A[σ] }} as ->; mauto 2.
Qed.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mcltt.

Lemma initial_env_glu_rel_exp : forall {Γ ρ Sb},
    initial_env Γ ρ ->
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊢s Id ® ρ ∈ Sb }}.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence;
    try solve [econstructor; mauto].

  assert (glu_rel_typ_with_sub i Γ A {{{ Id }}} ρ) as [] by mauto.
  functional_eval_rewrite_clear.
  econstructor; mauto.
  - match goal with
    | H: P Γ {{{ A[Id] }}} |- _ =>
        bulky_rewrite_in H
    end.
    eapply realize_glu_elem_bot; mauto.
    assert {{ ⊢ Γ }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 4.
    assert {{ Γ, A ⊢ A[Wk] ≈ A[Wk][Id] : Type@i }} as <- by mauto 3.
    assert {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} as <- by mauto.
    eapply var_glu_elem_bot; mauto.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A ⊢s Wk∘Id : Γ }} by mauto 4.
    assert {{ Γ, A ⊢s Id∘Wk ≈ Wk∘Id : Γ }} as <- by (transitivity {{{ Wk }}}; mauto 3).
    eapply glu_ctx_env_sub_monotone; mauto 4.
Qed.

(** Tactics for [glu_rel_*] *)

Ltac destruct_glu_rel_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : {{ ~?Δ ⊢s ~?σ ® ~?ρ ∈ ?sub_glu_rel0 }} |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        destruct (H _ _ _ H') as [];
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.
Ltac destruct_glu_rel_exp_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_exp_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_glu_rel_sub_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_sub_with_sub _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

(** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 : forall {Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ M : A }} ->
    exists i,
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      glu_rel_exp_with_sub i Δ M A σ ρ.
Proof.
  intros * ? [].
  destruct_conjs.
  eexists; intros.
  handle_functional_glu_ctx_env.
  mauto.
Qed.

Definition glu_rel_exp_clean_inversion2_result i Sb M A :=
  forall Δ σ ρ,
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_exp_with_sub i Δ M A σ ρ.

Lemma glu_rel_exp_clean_inversion2 : forall {i Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    glu_rel_exp_clean_inversion2_result i Sb M A.
Proof.
  unfold glu_rel_exp_clean_inversion2_result.
  intros * ? HA HM.
  eapply glu_rel_exp_clean_inversion1 in HA; [| eassumption].
  eapply glu_rel_exp_clean_inversion1 in HM; [| eassumption].
  destruct_conjs.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  econstructor; mauto 3.
  eapply glu_univ_elem_exp_conv; revgoals; mauto 3.
Qed.

Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   unfold glu_rel_exp_clean_inversion2_result in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Lemma glu_rel_exp_to_wf_exp : forall {Γ A M},
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  enough {{ Γ ⊢ M[Id] : A[Id] }} as HId; mauto 3 using glu_univ_elem_trm_escape.
Qed.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mcltt.

(** Lemmas about [glu_rel_sub] *)

Lemma glu_rel_sub_clean_inversion1 : forall {Γ Sb τ Γ'},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩s τ : Γ' }} ->
    exists Sb' : glu_sub_pred,
      glu_ctx_env Sb' Γ' /\ (forall (Δ : ctx) (σ : sub) (ρ : env), Sb Δ σ ρ -> glu_rel_sub_with_sub Δ τ Sb' σ ρ).
Proof.
  intros * ? [? []].
  destruct_conjs.
  handle_functional_glu_ctx_env.
  eexists; split; mauto 3.
  intros.
  rewrite_predicate_equivalence_right.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion2 : forall {Γ τ Γ' Sb'},
    {{ EG Γ' ∈ glu_ctx_env ↘ Sb' }} ->
    {{ Γ ⊩s τ : Γ' }} ->
    exists Sb : glu_sub_pred,
      glu_ctx_env Sb Γ /\ (forall (Δ : ctx) (σ : sub) (ρ : env), Sb Δ σ ρ -> glu_rel_sub_with_sub Δ τ Sb' σ ρ).
Proof.
  intros * ? [? [Sb'0]].
  destruct_conjs.
  handle_functional_glu_ctx_env.
  eexists; split; mauto 3.
  intros.
  assert (glu_rel_sub_with_sub Δ τ Sb'0 σ ρ) as [] by mauto 3.
  econstructor; mauto 3.
  rewrite_predicate_equivalence_right.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion3 : forall {Γ Sb τ Γ' Sb'},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env ↘ Sb' }} ->
    {{ Γ ⊩s τ : Γ' }} ->
    forall (Δ : ctx) (σ : sub) (ρ : env), Sb Δ σ ρ -> glu_rel_sub_with_sub Δ τ Sb' σ ρ.
Proof.
  intros * ? ? Hglu.
  eapply glu_rel_sub_clean_inversion2 in Hglu; [| eassumption].
  destruct_conjs.
  handle_functional_glu_ctx_env.
  intros.
  rewrite_predicate_equivalence_right.
  mauto 3.
Qed.

Ltac invert_glu_rel_sub H :=
  (unshelve eapply (glu_rel_sub_clean_inversion3 _ _) in H; shelve_unifiable; [eassumption | eassumption |])
  + (unshelve eapply (glu_rel_sub_clean_inversion2 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (unshelve eapply (glu_rel_sub_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (inversion H; subst).

Lemma glu_rel_sub_wf_sub : forall {Γ σ Δ},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [SbΓ [SbΔ]].
  destruct_conjs.
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }}) as [env_relΓ] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by mauto 3 using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_sub_with_sub.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_wf_sub : mcltt.
