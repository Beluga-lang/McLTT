From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Syntactic Require Import Corollaries.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import Realizability.
From Mcltt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Section glu_univ_elem_cumulativity.
  #[local]
  Lemma glu_univ_elem_cumulativity_ge : forall {i j a P P' El El'},
      i <= j ->
      {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
      {{ DG a ∈ glu_univ_elem j ↘ P' ↘ El' }} ->
      (forall Γ A, {{ Γ ⊢ A ® P }} -> {{ Γ ⊢ A ® P' }}) /\
        (forall Γ A M m, {{ Γ ⊢ M : A ® m ∈ El }} -> {{ Γ ⊢ M : A ® m ∈ El' }}) /\
        (forall Γ A M m, {{ Γ ⊢ A ® P }} -> {{ Γ ⊢ M : A ® m ∈ El' }} -> {{ Γ ⊢ M : A ® m ∈ El }}).
  Proof.
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
        assert (forall Γ A, {{ Γ ⊢ A ® IP }} -> {{ Γ ⊢ A ® IP' }}) by (eapply proj1; mauto).
        mauto.
      + rename a0 into c.
        rename equiv_a into equiv_c.
        match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
        apply_relation_equivalence.
        destruct_rel_mod_eval.
        handle_per_univ_elem_irrel.
        assert (forall Γ A, {{ Γ ⊢ A ® OP c equiv_c }} -> {{ Γ ⊢ A ® OP' c equiv_c }}) by (eapply proj1; mauto).
        enough {{ Δ ⊢ OT[σ,,m] ® OP c equiv_c }} by mauto.
        enough {{ Δ ⊢ m : IT[σ] ® c ∈ IEl }} by mauto.
        eapply IHHglu; mauto.
    - rename x into IP'.
      rename x0 into IEl'.
      rename x1 into OP'.
      rename x2 into OEl'.
      destruct_by_head pi_glu_exp_pred.
      handle_per_univ_elem_irrel.
      econstructor; intros; mauto 4.
      + assert (forall Γ A, {{ Γ ⊢ A ® IP }} -> {{ Γ ⊢ A ® IP' }}) by (eapply proj1; mauto).
        mauto.
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
        functional_eval_rewrite_clear.
        mauto.
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
      assert (forall Γ A M m, {{ Γ ⊢ A ® OP c equiv_c }} -> {{ Γ ⊢ M : A ® m ∈ OEl' c equiv_c }} -> {{ Γ ⊢ M : A ® m ∈ OEl c equiv_c }}) by (eapply proj2, proj2; eauto 3).
      assert {{ Δ ⊢ OT[σ,,m'] ® OP c equiv_c }} by mauto.
      enough {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® fa ∈ OEl' c equiv_c }} by mauto.
      assert {{ Δ ⊢ m' : IT[σ] ® c ∈ IEl' }} by (eapply IHHglu; mauto).
      assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Type@j }} as HITeq.
      {
        assert {{ Δ ⊢ IT[σ] ® glu_typ_top i a }} as [] by mauto 3.
        assert {{ Δ ⊢ IT0[σ] ® glu_typ_top j a }} as [] by mauto 3.
        match_by_head per_top_typ ltac:(fun H => destruct (H (length Δ)) as [? []]).
        clear_dups.
        functional_read_rewrite_clear.
        assert {{ Δ ⊢ IT[σ][Id] ≈ x1 : Type@i }} by mauto 4.
        assert {{ Δ ⊢ IT[σ] ≈ x1 : Type@i }} by mauto 4.
        assert {{ Δ ⊢ IT[σ] ≈ x1 : Type@j }} by mauto 4.
        assert {{ Δ ⊢ IT0[σ][Id] ≈ x1 : Type@j }} by mauto 4.
        enough {{ Δ ⊢ IT0[σ] ≈ x1 : Type@j }}; mautosolve 4.
      }
      assert {{ Δ ⊢ m' : IT0[σ] ® c ∈ IEl' }} by (rewrite <- HITeq; mauto).
      assert (exists ac, {{ $| a0 & c |↘ ac }} /\ {{ Δ ⊢ m[σ] m' : OT0[σ,,m'] ® ac ∈ OEl' c equiv_c }}) by mauto.
      destruct_conjs.
      functional_eval_rewrite_clear.
      assert {{ DG b ∈ glu_univ_elem j ↘ OP' c equiv_c ↘ OEl' c equiv_c }} by mauto.
      enough {{ Δ ⊢ OT[σ,,m'] ≈ OT0[σ,,m'] : Type@j }} as -> by mauto.
      assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }} by mauto.
      assert {{ Δ ⊢ OT0[σ,,m'] ® OP' c equiv_c }} by (eapply glu_univ_elem_trm_typ; mauto).
      assert {{ Δ ⊢ OT[σ,,m'] ® glu_typ_top i b }} as [] by mauto 3.
      assert {{ Δ ⊢ OT0[σ,,m'] ® glu_typ_top j b }} as [] by mauto 3.
      match_by_head per_top_typ ltac:(fun H => destruct (H (length Δ)) as [? []]).
      clear_dups.
      functional_read_rewrite_clear.
      assert {{ Δ ⊢ OT[σ,,m'][Id] ≈ x1 : Type@i }} by mauto 4.
      assert {{ Δ ⊢ OT[σ,,m'] ≈ x1 : Type@i }} by mauto 4.
      assert {{ Δ ⊢ OT[σ,,m'] ≈ x1 : Type@j }} by mauto 4.
      assert {{ Δ ⊢ OT0[σ,,m'][Id] ≈ x1 : Type@j }} by mauto 4.
      enough {{ Δ ⊢ OT0[σ,,m'] ≈ x1 : Type@j }}; mautosolve 4.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
      destruct_by_head neut_glu_typ_pred.
      econstructor; mauto.
    - destruct_by_head neut_glu_exp_pred.
      econstructor; mauto.
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
