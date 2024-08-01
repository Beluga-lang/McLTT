From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Syntactic Require Import Corollaries.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Lemma glu_univ_elem_per_univ_typ_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof.
  intros * [elem_rel Hper] Hglu Hglu' HA HA'.
  gen A' A Γ. gen El' El P' P.
  induction Hper using per_univ_elem_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    try solve [simpl in *; mauto 4].
  - destruct_by_head pi_glu_typ_pred.
    rename M into M'. rename IT into IT'. rename OT into OT'.
    rename x4 into IP'. rename x5 into IEl'. rename x6 into OP'. rename x7 into OEl'.
    rename M0 into M. rename IT0 into IT. rename OT0 into OT.
    rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl.
    assert {{ Γ ⊢ IT ® IP }}.
    {
      assert {{ Γ ⊢ IT[Id] ® IP }} by mauto.
      enough {{ Γ ⊢ IT[Id] ≈ IT : Type@i }} as <-; mauto.
    }
    assert {{ Γ ⊢ IT' ® IP' }}.
    {
      assert {{ Γ ⊢ IT'[Id] ® IP' }} by mauto.
      enough {{ Γ ⊢ IT'[Id] ≈ IT' : Type@i }} as <-; mauto.
    }
    do 2 bulky_rewrite1.
    assert {{ Γ ⊢ IT ≈ IT' : Type@i }} by mauto.
    enough {{ Γ, IT ⊢ OT ≈ OT' : Type@i }} by mauto 3.
    assert {{ Dom ⇑! A (length Γ) ≈ ⇑! A' (length Γ) ∈ in_rel }} as equiv_len_len' by (eapply per_bot_then_per_elem; mauto).
    assert {{ Dom ⇑! A (length Γ) ≈ ⇑! A (length Γ) ∈ in_rel }} as equiv_len_len by (eapply per_bot_then_per_elem; mauto).
    assert {{ Dom ⇑! A' (length Γ) ≈ ⇑! A' (length Γ) ∈ in_rel }} as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    rename a0 into b.
    rename a' into b'.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP d{{{ ⇑! A (length Γ) }}} equiv_len_len ↘ OEl d{{{ ⇑! A (length Γ) }}} equiv_len_len }} by mauto.
    assert {{ DG b' ∈ glu_univ_elem i ↘ OP' d{{{ ⇑! A' (length Γ) }}} equiv_len'_len' ↘ OEl' d{{{ ⇑! A' (length Γ) }}} equiv_len'_len' }} by mauto.
    assert {{ Γ, IT ⊢ OT ® OP d{{{ ⇑! A (length Γ) }}} equiv_len_len }}.
    {
      assert {{ Γ, IT ⊢ #0 : IT[Wk] ® !(length Γ) ∈ glu_elem_bot i A }} by eauto using var_glu_elem_bot.
      assert {{ Γ, IT ⊢ #0 : IT[Wk] ® ⇑! A (length Γ) ∈ IEl }} by (eapply realize_glu_elem_bot; mauto).
      assert {{ Γ, IT ⊢ OT[Wk,,#0] ≈ OT : Type@i }} by (bulky_rewrite1; mauto 3).
      eapply glu_univ_elem_typ_resp_equiv; mauto.
    }
    assert {{ Γ, IT ⊢ OT' ® OP' d{{{ ⇑! A' (length Γ) }}} equiv_len'_len' }}.
    {
      assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® !(length Γ) ∈ glu_elem_bot i A' }} by eauto using var_glu_elem_bot.
      assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® ⇑! A' (length Γ) ∈ IEl' }} by (eapply realize_glu_elem_bot; mauto).
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ® OP' d{{{ ⇑! A' (length Γ) }}} equiv_len'_len' }} by mauto.
      assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ≈ OT' : Type@i }} by (bulky_rewrite1; mauto 3).
      assert {{ ⊢ Γ, IT' ≈ Γ, IT }} by mauto.
      eapply glu_univ_elem_typ_resp_ctx_equiv; mauto.
      eapply glu_univ_elem_typ_resp_equiv; mauto.
    }
    mauto 3.
  - match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert {{ Γ ⊢ A[Id] ≈ A : Type@i }} as <- by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ A' : Type@i }} as <- by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ V : Type@i }} as -> by mauto 4.
    mauto 4.
Qed.
