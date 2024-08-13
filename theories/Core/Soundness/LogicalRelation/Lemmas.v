From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.Corollaries.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation.Core.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_univ_elem_typ_escape : forall {i j a P P' El El' Γ A A'},
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
Hint Resolve glu_univ_elem_typ_escape : mcltt.

Lemma glu_univ_elem_typ_escape_ge : forall {i j a P P' El El' Γ A A'},
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
Hint Resolve glu_univ_elem_typ_escape_ge : mcltt.

Lemma glu_univ_elem_typ_escape' : forall {i a P El Γ A A'},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_univ_elem_typ_escape' : mcltt.

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
      try assert {{ DF a ≈ a ∈ per_univ_elem j ↘ in_rel }} by mauto;
      invert_glu_univ_elem Hglu';
      handle_functional_glu_univ_elem;
      simpl in *;
      try solve [repeat split; intros; destruct_conjs; mauto 3 | intuition; mauto 4].

    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_typ_pred.
      econstructor; intros; mauto 4.
      + assert {{ Δ ⊢ IT[σ] ® IP }} by mauto.
        enough (forall Γ A, {{ Γ ⊢ A ® IP }} -> {{ Γ ⊢ A ® IP' }}) by mauto 4.
        eapply proj1...
      + rename a0 into c.
        rename equiv_a into equiv_c.
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        assert (forall Γ A, {{ Γ ⊢ A ® OP c equiv_c }} -> {{ Γ ⊢ A ® OP' c equiv_c }}) by (eapply proj1; mauto).
        enough {{ Δ ⊢ OT[σ,,m] ® OP c equiv_c }} by mauto.
        enough {{ Δ ⊢ m : IT[σ] ® c ∈ IEl }} by mauto.
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
      + rename b into c.
        rename equiv_b into equiv_c.
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        handle_per_univ_elem_irrel.
        destruct_rel_mod_eval.
        destruct_rel_mod_app.
        handle_per_univ_elem_irrel.
        eexists; split; mauto.
        assert (forall Γ A M m, {{ Γ ⊢ M : A ® m ∈ OEl c equiv_c }} -> {{ Γ ⊢ M : A ® m ∈ OEl' c equiv_c }}) by (eapply proj1, proj2; mauto).
        enough {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® fa ∈ OEl c equiv_c }} by mauto.
        assert {{ Δ ⊢ m' : IT[σ] ® c ∈ IEl }} by (eapply IHHglu; mauto).
        assert (exists ac, {{ $| a0 & c |↘ ac }} /\ {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® ac ∈ OEl c equiv_c }}) by mauto.
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
      rename b into c.
      rename equiv_b into equiv_c.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      handle_per_univ_elem_irrel.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      handle_per_univ_elem_irrel.
      rename a1 into b.
      eexists; split; mauto.
      assert (forall Γ A M m, {{ Γ ⊢ A ® OP c equiv_c }} -> {{ Γ ⊢ M : A ® m ∈ OEl' c equiv_c }} -> {{ Γ ⊢ M : A ® m ∈ OEl c equiv_c }}) by (eapply proj2, proj2; eauto).
      assert {{ Δ ⊢ OT[σ,,m'] ® OP c equiv_c }} by mauto.
      enough {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® fa ∈ OEl' c equiv_c }} by mauto.
      assert {{ Δ ⊢ m' : IT[σ] ® c ∈ IEl' }} by (eapply IHHglu; mauto).
      assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Type@j }} as HITeq by mauto 4.
      assert {{ Δ ⊢ m' : IT0[σ] ® c ∈ IEl' }} by (rewrite <- HITeq; mauto).
      assert (exists ac, {{ $| a0 & c |↘ ac }} /\ {{ Δ ⊢ m[σ] m' : OT0[σ,,m'] ® ac ∈ OEl' c equiv_c }}) by mauto.
      destruct_conjs.
      functional_eval_rewrite_clear.
      assert {{ DG b ∈ glu_univ_elem j ↘ OP' c equiv_c ↘ OEl' c equiv_c }} by mauto.
      assert {{ Δ ⊢ OT0[σ,,m'] ® OP' c equiv_c }} by (eapply glu_univ_elem_trm_typ; mauto).
      enough {{ Δ ⊢ OT[σ,,m'] ≈ OT0[σ,,m'] : Type@j }} as ->...
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
      destruct_by_head neut_glu_typ_pred.
      econstructor...
    - destruct_by_head neut_glu_exp_pred.
      econstructor...
  Qed.
End glu_univ_elem_cumulativity.

Corollary glu_univ_elem_typ_cumu_ge :  forall {i j a P P' El El' Γ A},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A ® P' }}.
Proof.
  intros.
  eapply glu_univ_elem_cumulativity_ge; mauto.
Qed.

Corollary glu_univ_elem_exp_cumu_ge :  forall {i j a P P' El El' Γ A M m},
    i <= j ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros * ? ? ?. gen m M A Γ.
  eapply glu_univ_elem_cumulativity_ge; mauto.
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
  eapply glu_univ_elem_cumulativity_ge; mauto.
Qed.

Lemma glu_univ_elem_exp_conv : forall {i j k a a' P P' El El' Γ A M m},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
    {{ Dom a ≈ a' ∈ per_univ k }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ A ® P' }} ->
    {{ Γ ⊢ M : A ® m ∈ El' }}.
Proof.
  intros * ? ? [] ? ?.
  assert {{ Dom a ≈ a' ∈ per_univ (max i k) }} by (eexists; mauto using per_univ_elem_cumu_max_right).
  assert (exists P El, {{ DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El }}) as [Pik [Elik]] by mauto using glu_univ_elem_cumu_max_left.
  assert {{ DG a' ∈ glu_univ_elem (max i k) ↘ Pik ↘ Elik }} by (erewrite <- glu_univ_elem_morphism_iff; try reflexivity; mauto).
  assert (i <= max i k) by lia.
  assert {{ Γ ⊢ M : A ® m ∈ Elik }} by (eapply glu_univ_elem_exp_cumu_ge; mauto).
  assert (exists P El, {{ DG a' ∈ glu_univ_elem (max j (max i k)) ↘ P ↘ El }}) as [Ptop [Eltop]] by mauto using glu_univ_elem_cumu_max_right.
  assert (max i k <= max j (max i k)) by lia.
  assert {{ Γ ⊢ M : A ® m ∈ Eltop }} by (eapply glu_univ_elem_exp_cumu_ge; mauto).
  assert (j <= max j (max i k)) by lia.
  eapply glu_univ_elem_exp_lower; mauto.
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
    try solve [simpl in *; mauto 4].
  - match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert {{ Γ ⊢ A[Id] ≈ A : Type@i }} as <- by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ A' : Type@i }} as <- by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ V : Type@i }} as -> by mauto 4.
    econstructor.
    mauto 4.
  - bulky_rewrite.
    mauto 3.
  - destruct_by_head pi_glu_typ_pred.
    rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl.
    rename M0 into M'. rename IT0 into IT'. rename OT0 into OT'.
    rename x3 into OP'. rename x4 into OEl'.
    assert {{ Γ ⊢ IT ® IP }}.
    {
      assert {{ Γ ⊢ IT[Id] ® IP }} by mauto.
      simpl in *.
      autorewrite with mcltt in *; mauto.
    }
    assert {{ Γ ⊢ IT' ® IP }}.
    {
      assert {{ Γ ⊢ IT'[Id] ® IP }} by mauto.
      simpl in *.
      autorewrite with mcltt in *; mauto.
    }
    do 2 bulky_rewrite1.
    assert {{ Γ ⊢ IT ≈ IT' : Type@i }} by mauto 4.
    enough {{ Γ, IT' ⊢ OT ⊆ OT' }} by mauto 3.
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len_len' by (eapply per_bot_then_per_elem; mauto).
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel }} as equiv_len_len by (eapply per_bot_then_per_elem; mauto).
    assert {{ Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto).
    handle_per_univ_elem_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    apply_relation_equivalence.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    rename a1 into b.
    rename a3 into b'.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP d{{{ ⇑! a (length Γ) }}} equiv_len_len ↘ OEl d{{{ ⇑! a (length Γ) }}} equiv_len_len }} by mauto.
    assert {{ DG b' ∈ glu_univ_elem i ↘ OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' ↘ OEl' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }} by mauto.
    assert {{ Γ, IT' ⊢ OT ® OP d{{{ ⇑! a (length Γ) }}} equiv_len_len }}.
    {
      assert {{ Γ, IT ⊢ #0 : IT[Wk] ® !(length Γ) ∈ glu_elem_bot i a }} by eauto using var_glu_elem_bot.
      assert {{ Γ, IT ⊢ #0 : IT[Wk] ® ⇑! a (length Γ) ∈ IEl }} by (eapply realize_glu_elem_bot; mauto).
      assert {{ ⊢ Γ, IT' ≈ Γ, IT }} as -> by mauto.
      assert {{ Γ, IT ⊢ OT[Wk,,#0] ≈ OT : Type@i }} as <- by (bulky_rewrite1; mauto 3).
      mauto.
    }
    assert {{ Γ, IT' ⊢ OT' ® OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }}.
    {
      assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® !(length Γ) ∈ glu_elem_bot i a' }} by eauto using var_glu_elem_bot.
      assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® ⇑! a' (length Γ) ∈ IEl }} by (eapply realize_glu_elem_bot; mauto).
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ® OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }} by mauto.
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ≈ OT' : Type@i }} as <- by (bulky_rewrite1; mauto 3).
      mauto.
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
    try solve [simpl in *; intuition].
  - rename A into a''.
    rename M into A.
    rename m into M.
    clear_dups.
    match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Γ)) as [V []]).
    econstructor; mauto 3.
    + econstructor; mauto 3.
    + intros.
      match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Δ)) as [? []]).
      functional_read_rewrite_clear.
      assert {{ Δ ⊢ A[σ] ⊆ A'[σ] }} by mauto 3.
      assert {{ Δ ⊢ M[σ] ≈ v : A[σ] }} by mauto.
      mauto.
  - simpl in *.
    destruct_conjs.
    intuition mauto 3.
    assert (exists P El, {{ DG m ∈ glu_univ_elem j ↘ P ↘ El }}) as [? [?]] by mauto.
    do 2 eexists; split; mauto.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mautosolve.
  - rename M into A.
    rename M0 into A'.
    rename m into M.
    rename IT0 into IT'. rename OT0 into OT'.
    rename x into IP. rename x0 into IEl.
    rename x1 into OP. rename x2 into OEl.
    rename x3 into OP'. rename x4 into OEl'.
    handle_per_univ_elem_irrel.
    econstructor; mauto 4.
    + enough {{ Sub Π a p B <: Π a' p' B' at i }} by (eapply per_elem_subtyping; try eassumption).
      econstructor; mauto.
    + intros.
      rename b into c.
      rename equiv_b into equiv_c.
      assert {{ Γ ⊢w Id : Γ }} by mauto.
      assert {{ Γ ⊢ IT ® IP }}.
      {
        assert {{ Γ ⊢ IT[Id] ® IP }} by mauto.
        simpl in *.
        autorewrite with mcltt in *; mauto.
      }
      assert {{ Γ ⊢ IT' ® IP }}.
      {
        assert {{ Γ ⊢ IT'[Id] ® IP }} by mauto.
        simpl in *.
        autorewrite with mcltt in *; mauto.
      }
      assert {{ Δ ⊢ IT[σ] ≈ IT'[σ] : Type@i }} by mauto 4 using glu_univ_elem_per_univ_elem_typ_escape.
      assert {{ Δ ⊢ m' : IT[σ] ® c ∈ IEl }} by (simpl; bulky_rewrite1; eassumption).
      assert (exists ac : domain, {{ $| a0 & c |↘ ac }} /\ OEl c equiv_c Δ (a_sub OT {{{ σ,, m' }}}) {{{ ~ (a_sub M σ) m' }}} ac) by mauto.
      destruct_conjs.
      eexists; split; mauto.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      rename a1 into b.
      rename a2 into b'.
      assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }} by mauto.
      assert {{ DG b' ∈ glu_univ_elem i ↘ OP' c equiv_c ↘ OEl' c equiv_c }} by mauto.
      assert {{ Δ ⊢ OT[σ,,m'] ® OP c equiv_c }} by (eapply glu_univ_elem_trm_typ; mauto).
      assert {{ Sub b <: b' at i }} by mauto 3.
      assert {{ Δ ⊢ OT[σ,,m'] ⊆ OT'[σ,,m'] }} by mauto 3.
      eapply H1; mauto 2.
Qed.

Lemma glu_ctx_env_per_env : forall {Γ Sb env_rel Δ σ p},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
    {{ Δ ⊢s σ ® p ∈ Sb }} ->
    {{ Dom p ≈ p ∈ env_rel }}.
Proof.
  intros * Hglu Hper.
  gen p σ Δ env_rel.
  induction Hglu; intros;
    invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto.

  rename i0 into j.
  inversion_clear_by_head cons_glu_sub_pred.
  assert {{ Dom p ↯ ≈ p ↯ ∈ tail_rel }} by (eapply IHHglu; mauto).
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  assert (exists P' El', {{ DG a ∈ glu_univ_elem (max i j) ↘ P' ↘ El' }}) as [? []] by mauto using glu_univ_elem_cumu_max_left.
  eexists; eapply glu_univ_elem_per_elem; mauto using per_univ_elem_cumu_max_right.
  assert (i <= max i j) by lia.
  eapply glu_univ_elem_exp_cumu_ge; mauto.
Qed.

Lemma glu_ctx_env_wf_ctx : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; intros; mauto.
Qed.

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
  assert (TSb -∙> TSb') by (eapply IHHglu; mauto).
  intros Δ σ p [].
  saturate_refl_for per_ctx_env.
  assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }}
    by (eapply glu_ctx_env_per_env; only 3: eassumption; eassumption).
  assert {{ Δ0 ⊢s Wk∘σ0 ® ρ ↯ ∈ TSb' }} by intuition.
  assert (glu_rel_typ_sub j Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ ↯ }}}) as [] by mauto.
  destruct_rel_typ.
  handle_functional_glu_univ_elem.
  rename a0 into a'.
  rename El0 into El'.
  rename P0 into P'.
  econstructor; mauto 4.
  assert (exists Pmax Elmax, {{ DG a ∈ glu_univ_elem (max i l) ↘ Pmax ↘ Elmax }}) as [Pmax [Elmax]]
      by mauto using glu_univ_elem_cumu_max_left.
  assert (i <= max i l) by lia.
  assert {{ Δ0 ⊢ #0[σ0] : A'[Wk∘σ0] ® ~(ρ 0) ∈ Elmax }}.
  {
    assert {{ Δ0 ⊢s Wk∘σ0 : Γ }} by mauto 4.
    assert {{ Δ0 ⊢ A'[Wk∘σ0] ≈ A[Wk∘σ0] : Type@(max i l) }} as -> by mauto 4 using lift_exp_eq_max_right.
    eapply glu_univ_elem_exp_cumu_ge; mauto.
  }
  eapply glu_univ_elem_exp_conv; intuition.
  eexists; mauto.
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

Lemma destruct_glu_rel_exp : forall {Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ M : A }} ->
    exists i,
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      glu_rel_exp_sub i Δ M A σ ρ.
Proof.
  intros * ? [Sb'].
  destruct_conjs.
  eexists; intros.
  handle_functional_glu_ctx_env.
  mauto.
Qed.
