From Coq Require Import Morphisms_Relations Relation_Definitions RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.SubstitutionCases Completeness.TermStructureCases Completeness.UniverseCases Semantic.Realizability System.
Import Domain_Notations.

Lemma valid_exp_nat : forall {Γ i},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ ℕ : Type@i }}.
Proof.
  intros * [env_relΓ].
  eexists_rel_exp.
  intros.
  eexists (per_univ _).
  split; econstructor; mauto; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_exp_nat : mcltt.

Lemma rel_exp_nat_sub : forall {Γ σ i Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ ℕ[σ] ≈ ℕ : Type@i }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  eexists (per_univ _).
  split; econstructor; mauto; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve rel_exp_nat_sub : mcltt.

Lemma valid_exp_zero : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ zero : ℕ }}.
Proof.
  intros * [env_relΓ].
  unshelve eexists_rel_exp; [constructor |].
  intros.
  eexists.
  split; econstructor; mauto.
  - per_univ_elem_econstructor; easy.
  - mauto.
Qed.

#[export]
Hint Resolve valid_exp_zero : mcltt.

Lemma rel_exp_zero_sub : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ zero[σ] ≈ zero : ℕ }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  eexists.
  split; econstructor; mauto.
  - per_univ_elem_econstructor; reflexivity.
  - mauto.
Qed.

#[export]
Hint Resolve rel_exp_zero_sub : mcltt.

Lemma rel_exp_succ_sub : forall {Γ σ Δ M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ M : ℕ }} ->
    {{ Γ ⊨ (succ M)[σ] ≈ succ (M[σ]) : ℕ }}.
Proof.
  intros * [env_relΓ] [env_relΔ].
  destruct_conjs.
  pose (env_relΔ0 := env_relΔ).
  handle_per_ctx_env_irrel.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists.
  split; econstructor; mauto.
  - per_univ_elem_econstructor; reflexivity.
  - mauto.
Qed.

#[export]
Hint Resolve rel_exp_succ_sub : mcltt.

Lemma rel_exp_succ_cong : forall {Γ M M'},
    {{ Γ ⊨ M ≈ M' : ℕ }} ->
    {{ Γ ⊨ succ M ≈ succ M' : ℕ }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists.
  split; econstructor; mauto.
  - per_univ_elem_econstructor; reflexivity.
  - mauto.
Qed.

#[export]
Hint Resolve rel_exp_succ_cong : mcltt.

Lemma eval_natrec_sub_neut : forall {Γ env_relΓ σ Δ env_relΔ MZ MZ' MS MS' A A' i m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Δ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Δ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Δ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}) o o' mz mz',
        {{ ⟦ σ ⟧s p ↘ o }} ->
        {{ ⟦ σ ⟧s p' ↘ o' }} ->
        {{ Dom o ≈ o' ∈ env_relΔ }} ->
        {{ ⟦ MZ ⟧ o ↘ mz }} ->
        {{ ⟦ MZ' ⟧ o' ↘ mz' }} ->
        {{ Dom rec m under o return A | zero -> mz | succ -> MS end ≈ rec m' under p' return A'[q σ] | zero -> mz' | succ -> MS'[q (q σ)] end ∈ per_bot }}).
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * equiv_Γ_Γ equiv_Δ_Δ [env_relΔℕ] [] [env_relΔℕA] equiv_m_m'.
  destruct_conjs.
  pose (env_relΔℕA0 := env_relΔℕA).
  pose (env_relΔℕ0 := env_relΔℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΔℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΔℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  rename p'2 into o.
  rename p'1 into o'.
  intro s.
  assert {{ Dom ⇑! ℕ s ≈ ⇑! ℕ s ∈ per_nat }} by mauto.
  assert {{ Dom o ↦ ⇑! ℕ s ≈ o' ↦ ⇑! ℕ s ∈ env_relΔℕ }} as HinΔℕs by (apply_relation_equivalence; mauto).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕs)).
  assert {{ Dom succ (⇑! ℕ s) ≈ succ (⇑! ℕ s) ∈ per_nat }} by mauto.
  assert {{ Dom o ↦ succ (⇑! ℕ s) ≈ o' ↦ succ (⇑! ℕ s) ∈ env_relΔℕ }} as HinΔℕsuccs by (apply_relation_equivalence; mauto).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs)).
  assert {{ Dom o ↦ ⇑! ℕ s ≈ o' ↦ ⇑! ℕ s ∈ env_relΔℕ }} as HinΔℕs' by (apply_relation_equivalence; mauto).
  assert {{ Dom o ↦ succ (⇑! ℕ s) ≈ o' ↦ succ (⇑! ℕ s) ∈ env_relΔℕ }} as HinΔℕsuccs' by (apply_relation_equivalence; mauto).
  assert {{ Dom zero ≈ zero ∈ per_nat }} by econstructor.
  assert {{ Dom o ↦ zero ≈ o' ↦ zero ∈ env_relΔℕ }} as HinΔℕz by (apply_relation_equivalence; mauto).
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕz)).
  destruct_conjs.
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  rename a' into a''.
  rename m'2 into a'.
  rename a1 into asucc.
  rename m'1 into asucc'.
  assert {{ Dom o ↦ ⇑! ℕ s ↦ ⇑! a (S s) ≈ o' ↦ ⇑! ℕ s ↦ ⇑! a' (S s) ∈ env_relΔℕA }} as HinΔℕA.
  {
    apply_relation_equivalence; eexists; eauto.
    unfold drop_env.
    repeat change (fun n => d{{{ ~?p ↦ ~?x ↦ ~?y }}} (S n)) with (fun n => d{{{ p ↦ x }}} n).
    repeat change (d{{{ ~?p ↦ ~?x ↦ ~?y }}} 0) with y.
    eapply per_bot_then_per_elem; mauto.
  }
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕA)).
  destruct_conjs.
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H (S s)) as [? []]).
  functional_read_rewrite_clear.
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ s) as [? []]; shelve_unifiable; [eassumption |]).
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ (S (S s))) as [? []]; shelve_unifiable; [eassumption |]).
  functional_read_rewrite_clear.
  destruct (equiv_m_m' s) as [? []].
  do 3 econstructor; mauto.
  repeat econstructor; mauto.
Qed.

Corollary eval_natrec_neut : forall {Γ env_relΓ MZ MZ' MS MS' A A' i m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}) mz mz',
        {{ ⟦ MZ ⟧ p ↘ mz }} ->
        {{ ⟦ MZ' ⟧ p' ↘ mz' }} ->
        {{ Dom rec m under p return A | zero -> mz | succ -> MS end ≈ rec m' under p' return A' | zero -> mz' | succ -> MS' end ∈ per_bot }}).
Proof.
  intros.
  assert {{ Dom rec m under p return A | zero -> mz | succ -> MS end ≈ rec m' under p' return ~ (a_sub A' {{{ q Id }}}) | zero -> mz' | succ -> ~ (a_sub MS' {{{ q (q Id) }}}) end ∈ per_bot }} by (eapply eval_natrec_sub_neut; mauto).
  etransitivity; [eassumption |].
  intros s.
  match_by_head per_bot ltac:(fun H => specialize (H s) as [? []]).
  eexists; split; [eassumption |].
  dir_inversion_by_head read_ne; subst.
  invert_rel_typ_body.
  mauto.
Qed.

Lemma eval_natrec_rel : forall {Γ env_relΓ MZ MZ' MS MS' A A' i m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_nat }} ->
    (forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}),
      forall (elem_rel : relation domain),
        rel_typ i A d{{{ p ↦ m }}} A d{{{ p' ↦ m' }}} elem_rel ->
        exists r r',
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\
            {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ p' ↘ r' }} /\
            {{ Dom r ≈ r' ∈ elem_rel }}).
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * equiv_Γ_Γ [env_relΓℕ] [] [env_relΓℕA] equiv_m_m'.
  assert {{ Γ, ℕ ⊨ A : Type@i }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; eexists; eauto).
  destruct_conjs.
  pose (env_relΓℕA0 := env_relΓℕA).
  pose (env_relΓℕ0 := env_relΓℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  induction equiv_m_m'; intros;
    (on_all_hyp: destruct_rel_by_assumption env_relΓ);
    destruct_by_head rel_typ;
    invert_rel_typ_body;
    destruct_by_head rel_exp;
    (rename m0 into mz || rename m into mz);
    rename m' into mz';
    try rename n into m';
    handle_per_univ_elem_irrel;
    rename p'2 into p;
    rename p'1 into p'.
  - do 2 eexists.
    mauto.
  - assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} by (apply_relation_equivalence; mauto).
    (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
    assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    functional_eval_rewrite_clear.
    unshelve epose proof (IHequiv_m_m' _ _ equiv_p_p' _ _) as [? [? [? []]]]; shelve_unifiable; [solve [mauto] |].
    rename x4 into r0.
    rename x5 into r'0.
    handle_per_univ_elem_irrel.
    assert {{ Dom p ↦ m ↦ r0 ≈ p' ↦ m' ↦ r'0 ∈ env_relΓℕA }} as HinΓℕA by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕA) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    mauto.
  - assert {{ Dom ⇑ ℕ m ≈ ⇑ ℕ m' ∈ per_nat }} by (econstructor; eassumption).
    assert {{ Dom p ↦ ⇑ ℕ m ≈ p' ↦ ⇑ ℕ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: mauto.
    eapply per_bot_then_per_elem; [eassumption |].
    eapply eval_natrec_neut; eauto.
    + do 2 eexists; [per_ctx_env_econstructor; eauto |]; apply_relation_equivalence; eauto.
    + eexists; eauto.
    + do 2 eexists; [do 2 (per_ctx_env_econstructor; eauto) |]; apply_relation_equivalence; eauto.
Qed.

Lemma rel_exp_natrec_cong_rel_typ: forall {Γ A A' i M M' env_relΓ},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : ℕ }} ->
    forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}),
    exists elem_rel, rel_typ i (a_sub A {{{ Id,, M }}}) p (a_sub A {{{ Id,, M }}}) p' elem_rel.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros.
  assert {{ ⊨ Γ }} by (eexists; eauto).
  assert {{ Γ ⊨ M ≈ M' : ℕ[Id] }} by (unshelve mauto; constructor).
  assert {{ Γ ⊨s Id,, M ≈ Id,, M' : Γ, ℕ }} by (unshelve mauto; constructor).
  assert {{ Γ ⊨s Id,, M : Γ, ℕ }} by mauto.
  assert {{ Γ ⊨ A[Id,,M] ≈ A'[Id,,M'] : Type@i[Id,,M] }} by mauto.
  assert {{ Γ ⊨ A[Id,,M] ≈ A'[Id,,M'] : Type@i }} as [] by mauto.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  assert {{ Dom p' ≈ p' ∈ env_relΓ }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  apply rel_exp_implies_rel_typ.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; eauto.
  eexists; etransitivity; [| symmetry]; eassumption.
Qed.

Lemma rel_exp_natrec_cong : forall {Γ MZ MZ' MS MS' A A' i M M'},
    {{ Γ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊨ M ≈ M' : ℕ }} ->
    {{ Γ ⊨ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * HAA' ? ? [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  assert (exists elem_rel, rel_typ i (a_sub A {{{ Id,, M }}}) p (a_sub A {{{ Id,, M }}}) p' elem_rel) as [elem_rel] by (eapply rel_exp_natrec_cong_rel_typ; eauto; econstructor; eauto).
  eexists.
  split; [eassumption |].
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  rename p'2 into p.
  rename p'1 into p'.
  rename m1 into m.
  enough (exists r r', {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\ {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ p' ↘ r' }} /\ elem_rel r r') by (destruct_conjs; mauto).
  eapply eval_natrec_rel; eauto.
  destruct HAA' as [env_relΓℕ].
  assert {{ Γ, ℕ ⊨ A ≈ A : Type@i }} as [] by (etransitivity; [| symmetry]; econstructor; eassumption).
  destruct_conjs.
  pose (env_relΓℕ0 := env_relΓℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; eauto).
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕ) as [? []]).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_natrec_cong : mcltt.

Lemma eval_natrec_sub_rel : forall {Γ env_relΓ σ Δ env_relΔ MZ MZ' MS MS' A A' i m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Δ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Δ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Δ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_nat }} ->
    (forall p p'
        (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }})
        o o'
        (elem_rel : relation domain),
        {{ ⟦ σ ⟧s p ↘ o }} ->
        {{ ⟦ σ ⟧s p' ↘ o' }} ->
        {{ Dom o ≈ o' ∈ env_relΔ }} ->
        rel_typ i A d{{{ o ↦ m }}} A d{{{ o' ↦ m' }}} elem_rel ->
        exists r r',
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ o ↘ r }} /\
            {{ rec m' ⟦return A'[q σ] | zero -> MZ'[σ] | succ -> MS'[q (q σ)] end⟧ p' ↘ r' }} /\
            {{ Dom r ≈ r' ∈ elem_rel }}).
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * equiv_Γ_Γ equiv_Δ_Δ [env_relΔℕ] [] [env_relΔℕA] equiv_m_m'.
  assert {{ Δ, ℕ ⊨ A : Type@i }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; econstructor; eassumption).
  destruct_conjs.
  pose (env_relΔℕA0 := env_relΔℕA).
  pose (env_relΔℕ0 := env_relΔℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΔℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΔℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  induction equiv_m_m'; intros;
    (on_all_hyp: destruct_rel_by_assumption env_relΔ);
    destruct_by_head rel_typ;
    invert_rel_typ_body;
    destruct_by_head rel_exp;
    (rename m0 into mz || rename m into mz);
    rename m' into mz';
    try rename n into m';
    handle_per_univ_elem_irrel;
    rename p'2 into o;
    rename p'1 into o'.
  - do 2 eexists.
    repeat split; mauto.
  - assert {{ Dom o ↦ m ≈ o' ↦ m' ∈ env_relΔℕ }} by (apply_relation_equivalence; mauto).
    (on_all_hyp: destruct_rel_by_assumption env_relΔℕ).
    assert {{ Dom o ↦ m ≈ o' ↦ m' ∈ env_relΔℕ }} as HinΓℕ by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    functional_eval_rewrite_clear.
    unshelve epose proof (IHequiv_m_m' _ _ equiv_p_p' _ _) as [? [? [? []]]]; shelve_unifiable; only 4: (solve [mauto]); eauto.
    rename x4 into r0.
    rename x5 into r'0.
    handle_per_univ_elem_irrel.
    assert {{ Dom o ↦ m ↦ r0 ≈ o' ↦ m' ↦ r'0 ∈ env_relΔℕA }} as HinΓℕA by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕA) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: econstructor; only 4: econstructor; mauto.
  - assert {{ Dom ⇑ ℕ m ≈ ⇑ ℕ m' ∈ per_nat }} by mauto.
    assert {{ Dom o ↦ ⇑ ℕ m ≈ o' ↦ ⇑ ℕ m' ∈ env_relΔℕ }} as HinΓℕ by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: repeat econstructor; eauto.
    eapply per_bot_then_per_elem; [eassumption |].
    eapply eval_natrec_sub_neut; only 7: eauto; eauto.
    + do 2 eexists; [per_ctx_env_econstructor; eauto |]; apply_relation_equivalence; eauto.
    + eexists. eauto.
    + do 2 eexists; [do 2 (per_ctx_env_econstructor; eauto) |]; apply_relation_equivalence; eauto.
Qed.

Lemma rel_exp_natrec_sub_rel_typ: forall {Γ σ Δ A i M env_relΓ},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ, ℕ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : ℕ }} ->
    forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}),
    exists elem_rel, rel_typ i (a_sub A {{{ σ,, M[σ] }}}) p (a_sub A {{{ σ,, M[σ] }}}) p' elem_rel.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros.
  assert {{ ⊨ Γ }} by (eexists; eauto).
  assert {{ ⊨ Δ }} by (eapply presup_rel_subst; eauto).
  assert {{ Γ ⊨ M[σ] : ℕ[σ] }} by mauto.
  assert {{ Γ ⊨s σ,, M[σ] : Δ, ℕ }} by (unshelve mauto; constructor).
  assert {{ Γ ⊨ A[σ,,M[σ]] : Type@i[σ,,M[σ]] }} by mauto.
  assert {{ Γ ⊨ A[σ,,M[σ]] : Type@i }} as [] by mauto.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  assert {{ Dom p' ≈ p' ∈ env_relΓ }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  apply rel_exp_implies_rel_typ.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  mauto.
Qed.

Lemma rel_exp_natrec_sub : forall {Γ σ Δ MZ MS A i M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ, ℕ ⊨ A : Type@i }} ->
    {{ Δ ⊨ MZ : A[Id,,zero] }} ->
    {{ Δ, ℕ, A ⊨ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Δ ⊨ M : ℕ }} ->
    {{ Γ ⊨ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΔ]]] HA ? ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (exists elem_rel, rel_typ i (a_sub A {{{ σ,, M[σ] }}}) p (a_sub A {{{ σ,, M[σ] }}}) p' elem_rel) as [elem_rel]
      by (eapply rel_exp_natrec_sub_rel_typ; only 5: eassumption; eauto; eexists; mauto).
  eexists.
  split; [eassumption |].
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  rename m1 into m.
  enough (exists r r',
             {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ o ↘ r }} /\
               {{ rec m' ⟦return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end⟧ p' ↘ r' }} /\
               {{ Dom r ≈ r' ∈ elem_rel }})
    by (destruct_conjs; econstructor; mauto).
  eapply eval_natrec_sub_rel; only 7,10: eassumption; mauto.
Qed.

#[export]
Hint Resolve rel_exp_natrec_sub : mcltt.

Lemma rel_exp_nat_beta_zero : forall {Γ MZ MS A},
    {{ Γ ⊨ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊨ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓℕA].
  destruct_conjs.
  assert {{ ⊨ Γ, ℕ }} as [env_relΓℕ] by (match_by_head (per_ctx_env env_relΓℕA) invert_per_ctx_env; eexists; eauto).
  destruct_conjs.
  pose (env_relΓℕ0 := env_relΓℕ).
  pose (env_relΓℕA0 := env_relΓℕA).
  match_by_head (per_ctx_env env_relΓℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  rename p'2 into p.
  rename p'1 into p'.
  destruct_by_head rel_exp.
  assert {{ Dom zero ≈ zero ∈ per_nat }} by econstructor.
  assert {{ Dom p ↦ zero ≈ p' ↦ zero ∈ env_relΓℕ }} by (apply_relation_equivalence; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_nat_beta_zero : mcltt.

Lemma rel_exp_nat_beta_succ_rel_typ : forall {Γ env_relΓ A i M},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ, ℕ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M : ℕ }} ->
    forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}),
    exists elem_rel : relation domain,
      rel_typ i (a_sub A {{{ Id,, succ M }}}) p (a_sub A {{{ Id,, succ M }}}) p' elem_rel.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros.
  assert {{ ⊨ Γ }} by (eexists; eauto).
  assert {{ Γ ⊨ ℕ : Type@0 }} by mauto.
  assert {{ Γ ⊨ ℕ ≈ ℕ[Id] : Type@0 }} by mauto.
  assert {{ Γ ⊨ succ M : ℕ[Id] }} by mauto.
  assert {{ Γ ⊨s Id,,succ M : Γ, ℕ }} by mauto.
  assert {{ Γ ⊨ A[Id,,succ M] : Type@i }} as [] by mauto.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  apply rel_exp_implies_rel_typ; eauto.
Qed.

Lemma rel_exp_nat_beta_succ : forall {Γ MZ MS A i M},
    {{ Γ, ℕ ⊨ A : Type@i }} ->
    {{ Γ ⊨ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊨ M : ℕ }} ->
    {{ Γ ⊨ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * HA ? ? [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  assert (exists elem_rel : relation domain,
             rel_typ i (a_sub A {{{ Id,, succ M }}}) p (a_sub A {{{ Id,, succ M }}}) p' elem_rel) as [elem_rel]
      by (eapply rel_exp_nat_beta_succ_rel_typ; eauto; eexists; mauto).
  eexists; split; [eassumption |].
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  rename p'2 into p.
  rename p'1 into p'.
  assert (exists r r',
             {{ rec succ m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\
               {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ p' ↘ r' }} /\
               {{ Dom r ≈ r' ∈ elem_rel }})
    by (eapply eval_natrec_rel; mauto).
  destruct_conjs.
  econstructor; mauto.
  dir_inversion_by_head eval_natrec; subst.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_nat_beta_succ : mcltt.
