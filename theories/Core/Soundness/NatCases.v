From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import ContextCases LogicalRelation Realizability SubstitutionCases SubtypingCases TermStructureCases UniverseCases.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_nat : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ ℕ : Type@i }}.
Proof.
  intros * [Sb].
  assert {{ ⊢ Γ }} by mauto.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem.
    apply_predicate_equivalence.
    cbn.
    mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mcltt.

Lemma glu_rel_exp_of_nat : forall {Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat Δ {{{ M[σ] }}} m) ->
    {{ Γ ⊩ M : ℕ }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  exists 0.
  intros.
  edestruct Hbody as [? []]; mauto.
  econstructor; mauto.
  - glu_univ_elem_econstructor; mauto; reflexivity.
  - simpl; split; mauto 3.
Qed.

Lemma glu_rel_exp_zero : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ zero : ℕ }}.
Proof.
  intros * [Sb].
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  eexists; split; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcltt.

Lemma glu_rel_exp_succ : forall {Γ M},
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ succ M : ℕ }}.
Proof.
  intros * HM.
  assert {{ Γ ⊢ M : ℕ }} by mauto.
  cbn in HM.
  destruct_conjs.
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbn in *.
  destruct_conjs.
  eexists; split; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mcltt.

Lemma cons_glu_ctx_env_sub_helper : forall {Γ SbΓ Δ σ ρ i A M m},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ cons_glu_sub_pred i Γ A SbΓ }}.
Proof.
  intros * ? ? HA HM ?.
  assert {{ Γ ⊩ Type@i : Type@(S i) }} by mauto 3.
  assert {{ Γ ⊢ M : A }} by mauto 2.
  assert {{ Γ ⊢ A : Type@i }} by mauto 2.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  econstructor; mauto 3;
    assert {{ Δ ⊢s Wk∘(σ,,M[σ]) ≈ σ : Γ }} as ->; mauto 3.
  enough {{ Δ ⊢ #0[σ,,M[σ]] ≈ M[σ] : A[σ] }} as ->; mauto 3.
Qed.

#[export]
Hint Resolve cons_glu_ctx_env_sub_helper : mcltt.

Lemma glu_rel_exp_natrec_helper : forall {i Γ SbΓ A MZ MS},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    forall {Δ M m},
      glu_nat Δ M m ->
      forall {σ p am P El},
        {{ Δ ⊢s σ ® p ∈ SbΓ }} ->
        {{ ⟦ A ⟧ p ↦ m ↘ am }} ->
        {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
        exists r,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\
            {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA HMZ HMS.
  (* common things *)
  assert {{ ⊩ Γ }} by mauto 3.
  assert {{ ⊩ Γ, ℕ }} by mauto 3.
  assert {{ ⊩ Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 3.
  assert {{ Γ ⊩s Id : Γ }} by mauto 3.
  assert {{ Γ ⊢s Id : Γ }} by mauto 3.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[Id] }} by mauto 4.
  assert {{ Γ ⊢ Type@i[Id] ⊆ Type@i }} by mauto 3.
  assert {{ Γ ⊩ ℕ : Type@i }} as Hℕ by mauto 3.
  assert {{ Γ ⊩ ℕ[Id] : Type@i }} by mauto 4.
  assert {{ Γ ⊩ zero : ℕ }} by mauto 3.
  assert {{ Γ ⊩ zero : ℕ[Id] }} by mauto 4.
  assert {{ Γ ⊩s Id,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ Type@i[Id,,zero] ⊆ Type@i }} by mauto 3.
  assert {{ Γ ⊩ A[Id,,zero] : Type@i[Id,,zero] }} by mauto 3.
  assert {{ Γ ⊩ A[Id,,zero] : Type@i }} by mauto 3.
  invert_glu_rel_exp HMZ.
  pose (SbΓℕ := cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity).
  assert {{ Γ, ℕ ⊩ Type@i : Type@(S i) }} by mauto 3.
  pose proof HA.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred i {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env ↘ SbΓℕA }} by (econstructor; mauto 3; try reflexivity).
  assert {{ Γ, ℕ ⊩s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩s Wk : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ #1 : ℕ[Wk][Wk] }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ⊆ ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ #1 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ succ #1 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ ≈ ℕ[Wk∘Wk] : Type@0 }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ ⊆ ℕ[Wk∘Wk] }} by mauto 3.
  assert {{ Γ ⊩ ℕ : Type@0 }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ ℕ[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ Type@i[Wk∘Wk] ⊆ Type@i }} by mauto 4.
  assert {{ Γ, ℕ, A ⊩ ℕ[Wk∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ succ #1 : ℕ[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ Type@i[Wk∘Wk,,succ #1] ⊆ Type@i }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i[Wk∘Wk,,succ #1] }} by mauto 3.
  assert {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i }} by mauto 3.
  invert_glu_rel_exp HMS.
  induction 1; intros; rename m into M; rename Γ0 into Δ.
  - (* glu_nat_zero *)
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    rename p'0 into p.
    rename m into mz.
    eexists mz; split; mauto 3.
    handle_functional_glu_univ_elem.
    assert {{ Δ ⊢s σ : Γ }} by mauto 2.
    assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 2.
    assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 2.
    assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 2.
    assert {{ Δ ⊢s σ,,M ≈ σ,,zero : Γ, ℕ }} by mauto 3.
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by (gen_presups; eassumption).
    assert {{ Δ ⊢ A[σ,,M] ≈ A[q σ][Id,,zero] : Type@i }} as -> by (autorewrite with mcltt; mauto 3).
    assert
      {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,zero] }} as ->.
    {
      let H := fresh "H" in
      assert
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,M] }} as H by admit;
      autorewrite with mcltt in H.
      - autorewrite with mcltt; mauto 3.
      - mauto.
      - econstructor; mauto.
    }
    assert
      {{ Δ ⊢ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MZ[σ] : A[q σ][Id,,zero] }} as -> by admit.
    assert {{ Δ ⊢s σ ≈ Id∘σ : Γ }} by mauto 3.
    assert {{ Δ ⊢s σ,,zero ≈ (Id∘σ),,zero[σ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ ⊢s σ,,M ≈ (Id∘σ),,zero[σ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ ⊢s (Id∘σ),,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
    assert {{ Δ ⊢s σ,,zero ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
    assert {{ Δ ⊢s σ,,zero : Γ, ℕ }} by mauto 4.
    assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] : Type@i }} as -> by (autorewrite with mcltt; mauto 3).
    eassumption.
  - (* glu_nat_succ *)
    rename m' into M'.
    rename a into m'.
    assert {{ Δ ⊢s σ,,M' ® p ↦ m' ∈ SbΓℕ }}.
    {
      assert {{ Δ ⊢ M' : ℕ }} by mauto 3.
      unfold SbΓℕ.
      econstructor; mauto 3.
      - glu_univ_elem_econstructor; reflexivity.
      - simpl; split; mauto 3.
        + mauto. (* TODO: optimize this case *)
        + eapply glu_nat_resp_exp_eq; mauto 4.
      - enough {{ Δ ⊢s Wk ∘ (σ,, M') ≈ σ : Γ }} as -> by eassumption.
        mauto 3.
    }
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    clear_dups.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    rename p'0 into p.
    rename m into am'.
    rename m0 into mz.
    rename a0 into az.
    rename H54 into P'.
    rename H58 into El'.
    assert (exists r, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\ {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® r ∈ El' }}) as [r' []] by mauto 3.
    assert {{ Δ ⊢s σ,,M',,rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ® p ↦ m' ↦ r' ∈ SbΓℕA }}.
    {
      unfold SbΓℕA.
      econstructor; try eassumption.
      - econstructor; mauto 3.
        admit. (* Syntactic judgement *)
      - admit. (* Syntactic rewritings *)
      - admit. (* Syntactic rewritings *)
    }
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    clear_dups.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    rename p'0 into p.
    rename m into ms.
    exists ms; split; mauto 3.
    admit. (* Now syntactic quality *)
  - (* glu_nat_neut *)
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    rename p'0 into p.
    rename m into mz.
    rename c into m.
    eexists; split; mauto 3.
    enough {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® rec m under p return A | zero -> mz | succ -> MS end ∈ glu_elem_bot i am }} by (eapply realize_glu_elem_bot; mauto 3).
    econstructor; mauto 3.
    + admit. (* syntactic judgement *)
    + assert {{ Δ ⊢s σ,,M ® p ↦ ⇑ ℕ m ∈ SbΓℕ }}.
      {
        match_by_head1 (per_bot m m) ltac:(fun H => destruct (H (length Δ)) as [V []]).
        assert {{ Δ ⊢w Id : Δ }} by mauto 4.
        assert {{ Δ ⊢ M[Id] ≈ V : ℕ }} by mauto 3.
        assert {{ Δ ⊢ M[Id] : ℕ }} by (gen_presups; mauto 3).
        assert {{ Δ ⊢ M : ℕ }} by mauto 3.
        unfold SbΓℕ.
        econstructor; mauto 3.
        - glu_univ_elem_econstructor; reflexivity.
        - simpl; split; mauto 3.
          + mauto. (* TODO: optimize this case *)
          + eapply glu_nat_resp_exp_eq; mauto 4.
        - enough {{ Δ ⊢s Wk ∘ (σ,, M) ≈ σ : Γ }} as -> by eassumption.
          mauto 3.
      }
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      apply_predicate_equivalence.
      clear_dups.
      unfold univ_glu_exp_pred' in *.
      destruct_conjs.
      handle_functional_glu_univ_elem.
      eassumption.
    + assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top; eassumption).
      handle_functional_glu_univ_elem.
      assert {{ ⊨ Γ }} as [env_relΓ] by mauto using completeness_fundamental_ctx.
      assert {{ Γ, ℕ ⊨ A : Type@i }} as [env_relΓℕ] by mauto using completeness_fundamental_exp.
      assert {{ Γ, ℕ, A ⊨ MS : A[Wk∘Wk,,succ #1] }} as [env_relΓℕA] by mauto using completeness_fundamental_exp.
      destruct_conjs.
      pose env_relΓℕA.
      match_by_head (per_ctx_env env_relΓℕA) ltac:(fun H => invert_per_ctx_env H).
      match_by_head (per_ctx_env env_relΓℕ) ltac:(fun H => invert_per_ctx_env H).
      intros s.
      enough (exists r, {{ Rne rec m under p return A | zero -> mz | succ -> MS end in s ↘ r }}) as [] by (eexists; split; eassumption).
      assert {{ Dom p ≈ p ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
      destruct_rel_typ.
      invert_rel_typ_body.
      assert {{ Dom ! s ≈ ! s ∈ per_bot }} by admit. (* trivial *)
      assert {{ Dom p ↦ ⇑! ℕ s ≈ p ↦ ⇑! ℕ s ∈ env_relΓℕ }} by (apply_relation_equivalence; unshelve eexists; simpl; intuition).
      assert {{ Dom p ↦ succ ⇑! ℕ s ≈ p ↦ succ ⇑! ℕ s ∈ env_relΓℕ }} by (apply_relation_equivalence; unshelve eexists; simpl; intuition).
      destruct_rel_typ.
      invert_rel_typ_body.
      rename a1 into asucc.
      rename a2 into as'.
      assert {{ Dom p ↦ ⇑! ℕ s ↦ ⇑! as' (S s) ≈ p ↦ ⇑! ℕ s ↦ ⇑! as' (S s) ∈ env_relΓℕA }} as HΓℕA
          by (apply_relation_equivalence; unshelve eexists; simpl; intuition; eapply per_bot_then_per_elem; mauto 3).
      apply_relation_equivalence.
      (on_all_hyp_rev: fun H => destruct (H _ _ HΓℕA)).
      destruct_conjs.
      destruct_by_head rel_typ.
      destruct_by_head rel_exp.
      invert_rel_typ_body.
      rename m0 into ms.
      assert {{ Dom as' ≈ as' ∈ per_top_typ }} as [? []]%(fun {a} (f : per_top_typ a a) => f (S s)) by mauto 3.
      assert {{ Dom ⇓ asucc ms ≈ ⇓ asucc ms ∈ per_top }} as [? []]%(fun {a} (f : per_top a a) => f (S (S s))) by mauto 3.
      match_by_head1 (per_top d{{{ ⇓ a mz }}} d{{{ ⇓ a mz }}}) ltac:(fun H => destruct (H s) as [? []]).
      match_by_head1 (per_bot m m) ltac:(fun H => destruct (H s) as [? []]).
      eexists.
      mauto.
    + intros Δ' τ w **.
      match_by_head read_ne ltac:(fun H => directed inversion_clear H).
      rename MZ0 into MZ'.
      rename M0 into M'.
      assert {{ Δ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[σ,,M][τ] }} as -> by admit. (* Syntactic eq *)
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ B' : Type@i }} by admit.
      assert {{ Δ' ⊢ MZ[σ][τ] ≈ MZ' : A[q σ][q τ][Id,,zero] }} by admit.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS' : A[q σ][q τ][Wk∘Wk,,succ #1] }} by admit.
      assert {{ Δ' ⊢ M[σ][τ] ≈ M' : ℕ }} by admit.
      assert {{ Δ' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[σ,,M][τ] : Type@i }} by admit.
      eapply wf_exp_eq_conv'; mauto 3.
Admitted.

Lemma glu_rel_exp_natrec : forall {Γ i A MZ MS M},
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  intros * HA HMZ HMS HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@i }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity).
  assert {{ Γ, ℕ ⊩ Type@i : Type@(S i) }} by mauto 3.
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_exp HA.
  eexists; split; mauto.
  exists i.
  intros.
  destruct_glu_rel_exp_with_sub.
  assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  clear_dups.
  inversion_clear_by_head nat_glu_exp_pred.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  match_by_head nat_glu_typ_pred ltac:(fun H => clear H).
  rename m0 into a.
  rename H13 into P.
  rename H14 into El.
  enough (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ~ r }} /\ El Δ {{{ A[Id,, M][σ] }}} {{{ rec M return A | zero -> MZ | succ -> MS end[σ] }}} r) as [? []] by (eapply mk_glu_rel_exp_with_sub; mauto 3).
  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ~ r }} /\ El Δ {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4).
  eexists; split; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ M[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s Id,,M[σ] : Δ, ℕ }} by mauto 4.
  assert {{ Δ ⊢s σ ≈ σ∘Id : Γ }} by mauto 3.
  assert {{ Δ ⊢s σ,,M[σ] ≈ (σ∘Id),,M[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,M[σ] ≈ (Id,,M)∘σ : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] : Type@i }} as <- by (autorewrite with mcltt; mauto 4).
  assert {{ Δ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 3).
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mcltt.
