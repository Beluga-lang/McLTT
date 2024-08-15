From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Syntactic Require Import Corollaries.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Cumulativity Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation EquivalenceLemmas.
Import Domain_Notations.

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
