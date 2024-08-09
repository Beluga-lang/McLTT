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
    assert {{ Γ ⊢ IT ≈ IT' : Type@i }} by mauto 4 using glu_univ_elem_per_univ_typ_escape.
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

(* Lemma glu_univ_elem_per_subtyp_typ_if : forall {i Γ Sb Δ σ p A A' a a' P P' El El'}, *)
(*     {{ EG Γ ∈ glu_ctx_env ↘ Sb }} -> *)
(*     {{ Δ ⊢s σ ® p ∈ Sb }} -> *)
(*     {{ ⟦ A ⟧ p ↘ a }} -> *)
(*     {{ ⟦ A' ⟧ p ↘ a' }} -> *)
(*     {{ Sub a <: a' at i }} -> *)
(*     {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> *)
(*     {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} -> *)
(*     {{ Δ ⊢ A[σ] ® P }} -> *)
(*     {{ Δ ⊢ A'[σ] ® P' }}. *)
(* Proof. *)
(*   intros * HSb Hσ Heval Heval' Hsubtyp Hglu Hglu' HA. *)
(*   gen El' El P' P. gen A' A p σ. gen Δ Sb Γ. *)
(*   induction Hsubtyp using per_subtyp_ind; intros; subst; *)
(*     saturate_refl_for per_univ_elem; *)
(*     invert_glu_univ_elem Hglu; *)
(*     handle_functional_glu_univ_elem; *)
(*     handle_per_univ_elem_irrel; *)
(*     destruct_by_head pi_glu_typ_pred; *)
(*     saturate_glu_by_per; *)
(*     invert_glu_univ_elem Hglu'; *)
(*     handle_functional_glu_univ_elem; *)
(*     try solve [simpl in *; mauto 4]. *)
(*   - inversion_by_head neut_glu_typ_pred. *)
(*     econstructor; mauto. *)

Lemma glu_univ_elem_per_subtyp_trm_if : forall {i a a' P P' El El' Γ A A' M m},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Γ ⊢ M : A' ® m ∈ El' }}.
Proof.
  intros * Hsubtyp Hglu Hglu'.
  gen m M A Γ. gen El' El P' P.
  induction Hsubtyp using per_subtyp_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    handle_functional_glu_univ_elem;
    handle_per_univ_elem_irrel;
    destruct_by_head pi_glu_typ_pred;
    saturate_glu_by_per;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem;
    try solve [simpl in *; intuition].
  - destruct_by_head neut_glu_exp_pred.
    destruct_by_head neut_glu_typ_pred.
    rename A into a''.
    rename M into A.
    rename m into M.
    clear_dups.
    match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Γ)) as [V []]).
    assert {{ Γ ⊢ A ≈ A' : Type@i }}.
    {
      assert {{ Γ ⊢ A'[Id] ≈ V : Type@i }} by mauto 4.
      assert {{ Γ ⊢ A[Id] ≈ V : Type@i }} by mauto 4.
      autorewrite with mcltt in *.
      mauto.
    }
    econstructor; mauto 3.
    + econstructor; mauto 3.
    + intros.
      match_by_head1 (per_bot b b') ltac:(fun H => destruct (H (length Δ)) as [? []]).
      functional_read_rewrite_clear.
      assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} by mauto.
      assert {{ Δ ⊢ M[σ] ≈ v : A[σ] }} by mauto.
      mauto.
  - simpl in *.
    assert {{ Γ ⊢ A ⊆ A' }}
      by (transitivity {{{ Type@i }}}; mauto 3; transitivity {{{ Type@j }}}; mauto 3).
    destruct_conjs.
    intuition mauto 3.
    assert (exists P El, {{ DG m ∈ glu_univ_elem j ↘ P ↘ El }}) as [? [?]].
    {
      assert {{ Dom m ≈ m ∈ per_univ i }} as [] by mauto using glu_univ_elem_per_univ.
      mauto using per_univ_glu_univ_elem.
    }
    do 2 eexists; split; mauto.
    eapply glu_univ_elem_typ_cumu_ge; revgoals; mautosolve.
  - eexists; handle_functional_glu_univ_elem.

(* Proof. *)
(*   intros * Hsubtyp Hglu Hglu'. *)
(*   gen A Γ. gen El' El P' P. *)
(*   induction Hsubtyp using per_subtyp_ind; intros; subst; *)
(*     saturate_refl_for per_univ_elem; *)
(*     invert_glu_univ_elem Hglu; *)
(*     handle_functional_glu_univ_elem; *)
(*     handle_per_univ_elem_irrel; *)
(*     destruct_by_head pi_glu_typ_pred; *)
(*     saturate_glu_by_per; *)
(*     invert_glu_univ_elem Hglu'; *)
(*     try solve [eexists; handle_functional_glu_univ_elem; simpl in *; mauto 4]; *)
(*     handle_functional_glu_univ_elem. *)
(*   - exists A; handle_functional_glu_univ_elem. *)
(*     split; firstorder. *)
(*     match_by_head (per_bot b b') ltac:(fun H => specialize (H (length Δ)) as [V' []]). *)
(*     functional_read_rewrite_clear. *)
(*     mauto. *)
(*   - handle_per_univ_elem_irrel. *)
(*     rename x into IP. rename x0 into IEl. rename x1 into OP. rename x2 into OEl. *)
(*     rename x3 into OP'. rename x4 into OEl'. *)
(*     assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len_len' by (eapply per_bot_then_per_elem; mauto). *)
(*     assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel }} as equiv_len_len by (eapply per_bot_then_per_elem; mauto). *)
(*     assert {{ Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv_len'_len' by (eapply per_bot_then_per_elem; mauto). *)
(*     match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H). *)
(*     apply_relation_equivalence. *)
(*     destruct_rel_mod_eval. *)
(*     handle_per_univ_elem_irrel. *)
(*     rename a1 into b. *)
(*     rename a3 into b'. *)
(*     assert {{ DG b ∈ glu_univ_elem i ↘ OP d{{{ ⇑! a (length Γ) }}} equiv_len_len ↘ OEl d{{{ ⇑! a (length Γ) }}} equiv_len_len }} by mauto. *)
(*     assert {{ DG b' ∈ glu_univ_elem i ↘ OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' ↘ OEl' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }} by mauto. *)
(*     assert {{ Γ ⊢ IT ® IP }}. *)
(*     { *)
(*       assert {{ Γ ⊢ IT[Id] ® IP }} by mauto. *)
(*       simpl in *. *)
(*       autorewrite with mcltt in *; mauto. *)
(*     } *)
(*     assert {{ Γ, IT ⊢ OT ® OP d{{{ ⇑! a (length Γ) }}} equiv_len_len }}. *)
(*     { *)
(*       assert {{ Γ, IT ⊢ #0 : IT[Wk] ® !(length Γ) ∈ glu_elem_bot i a }} by mauto using var_glu_elem_bot. *)
(*       assert {{ Γ, IT ⊢ #0 : IT[Wk] ® ⇑! a (length Γ) ∈ IEl }} by (eapply realize_glu_elem_bot; mauto). *)
(*       assert {{ Γ, IT ⊢ OT[Wk,,#0] ≈ OT : Type@i }} as <- by (bulky_rewrite1; mauto 3). *)
(*       mauto. *)
(*     } *)
(*     assert (exists OT', {{ Γ, IT ⊢ OT' ® OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' }}) as [OT'] by mauto. *)
(*     assert {{ Γ, IT ⊢ OT' : Type@i }} by mauto 3 using glu_univ_elem_univ_lvl. *)
(*     exists {{{ Π IT OT' }}}. *)
(*     apply_predicate_equivalence. *)
(*     econstructor; mauto 4. *)
(*     (* stuck.... *) *)
(*     intros. *)
(*     destruct_rel_mod_eval. *)
(*     handle_per_univ_elem_irrel. *)
(*     rename a1 into c. *)
(*     rename equiv_a into equiv_c. *)
(*     rename a2 into b0. *)
(*     rename a7 into b'0. *)
(*     assert (exists OT'', {{ Δ ⊢ OT'' ® OP' c equiv_c }}) as [OT''] by mauto. *)
(*     assert {{ Γ, IT ⊢ OT' ® glu_typ_top i b' }} as [] by mauto 4. *)
(*     assert {{ Δ ⊢ OT'' ® glu_typ_top i b'0 }} as [] by mauto 4. *)
(*     assert {{ DG b'0 ∈ glu_univ_elem i ↘ OP' c equiv_c ↘ OEl' c equiv_c }} by mauto. *)
(*     enough {{ Δ ⊢ OT'[σ,,m] ≈ OT'' : Type@i }} as -> by mauto. *)
(*     (* assert {{ Δ ⊢ OT''[Id] ≈ OT'' : Type@i }} as <- by mauto. *) *)
(*     (* assert {{ Δ ⊢ m : IT[σ] }} by mauto 3 using glu_univ_elem_trm_escape. *) *)
(*     (* assert {{ Δ ⊢s σ : Γ }} by mauto. *) *)
(*     (* assert {{ Δ ⊢s Wk∘(Id,,m) ≈ Id : Δ }} as <- by mauto 3. *) *)
(*     (* assert {{ Γ, IT ⊢ OT[Wk,,#0] ≈ OT : Type@i }} as <- by (bulky_rewrite1; mauto 3). *) *)
(* Abort. *)
