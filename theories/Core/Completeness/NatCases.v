From Coq Require Import Morphisms_Relations Relation_Definitions RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.TermStructureCases Semantic.Realizability System.
Import Domain_Notations.

Lemma valid_exp_nat : forall {Γ i},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ ℕ : Type@i }}.
Proof.
  intros * [env_relΓ].
  eexists_rel_exp.
  intros.
  eexists (per_univ _).
  split; [> econstructor; only 1-2: repeat econstructor ..]; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

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
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

Lemma valid_exp_zero : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ zero : ℕ }}.
Proof.
  intros * [env_relΓ].
  unshelve eexists_rel_exp; [constructor |].
  intros.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor ..].
  - per_univ_elem_econstructor; reflexivity.
  - econstructor.
Qed.

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
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor.
Qed.

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
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor; eassumption.
Qed.

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
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor; eassumption.
Qed.

Lemma eval_natrec_neut : forall {Γ env_relΓ MZ MZ' MS MS' A A' i m m'},
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
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * equiv_Γ_Γ [env_relΓℕ] [] [env_relΓℕA] equiv_m_m'.
  destruct_conjs.
  pose (env_relΓℕA0 := env_relΓℕA).
  pose (env_relΓℕ0 := env_relΓℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  rename p'2 into p.
  rename p'1 into p'.
  intro s.
  assert {{ Dom ⇑! ℕ s ≈ ⇑! ℕ s ∈ per_nat }} by repeat econstructor.
  assert {{ Dom p ↦ ⇑! ℕ s ≈ p' ↦ ⇑! ℕ s ∈ env_relΓℕ }} as HinΓℕs by (apply_relation_equivalence; eexists; eauto).
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕs)).
  assert {{ Dom succ (⇑! ℕ s) ≈ succ (⇑! ℕ s) ∈ per_nat }} by repeat econstructor.
  assert {{ Dom p ↦ succ (⇑! ℕ s) ≈ p' ↦ succ (⇑! ℕ s) ∈ env_relΓℕ }} as HinΓℕsuccs by (apply_relation_equivalence; eexists; eauto).
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕsuccs)).
  assert {{ Dom p ↦ ⇑! ℕ s ≈ p' ↦ ⇑! ℕ s ∈ env_relΓℕ }} as HinΓℕs' by (apply_relation_equivalence; eexists; eauto).
  assert {{ Dom p ↦ succ (⇑! ℕ s) ≈ p' ↦ succ (⇑! ℕ s) ∈ env_relΓℕ }} as HinΓℕsuccs' by (apply_relation_equivalence; eexists; eauto).
  assert {{ Dom zero ≈ zero ∈ per_nat }} by econstructor.
  assert {{ Dom p ↦ zero ≈ p' ↦ zero ∈ env_relΓℕ }} as HinΓℕz by (apply_relation_equivalence; eexists; eauto).
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕsuccs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕz)).
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
  assert {{ Dom p ↦ ⇑! ℕ s ↦ ⇑! a (S s) ≈ p' ↦ ⇑! ℕ s ↦ ⇑! a' (S s) ∈ env_relΓℕA }} as HinΓℕA.
  {
    apply_relation_equivalence; eexists; eauto.
    unfold drop_env.
    repeat change (fun n => d{{{ ~?p ↦ ~?x ↦ ~?y }}} (S n)) with (fun n => d{{{ p ↦ x }}} n).
    repeat change (d{{{ ~?p ↦ ~?x ↦ ~?y }}} 0) with y.
    eapply per_bot_then_per_elem; [eassumption |].
    apply var_per_bot.
  }
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕA)).
  destruct_conjs.
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H (S s)) as [? []]).
  functional_read_rewrite_clear.
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _) as [? []]; [| | eassumption | exact s |]).
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _) as [? []]; [| | eassumption | exact (S (S s)) |]).
  functional_read_rewrite_clear.
  destruct (equiv_m_m' s) as [? []].
  do 3 econstructor; eauto.
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
  assert {{ Γ, ℕ ⊨ A : Type@i }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; econstructor; eassumption).
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
    repeat split; only 1-2: econstructor; eauto.
  - assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} by (apply_relation_equivalence; eexists; eauto).
    (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
    assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    functional_eval_rewrite_clear.
    unshelve epose proof (IHequiv_m_m' _ _ equiv_p_p' _ _) as [? [? [? []]]]; [| econstructor; solve [eauto] |].
    rename x4 into r0.
    rename x5 into r'0.
    handle_per_univ_elem_irrel.
    assert {{ Dom p ↦ m ↦ r0 ≈ p' ↦ m' ↦ r'0 ∈ env_relΓℕA }} as HinΓℕA by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕA) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: econstructor; eauto.
  - assert {{ Dom ⇑ ℕ m ≈ ⇑ ℕ m' ∈ per_nat }} by (econstructor; eassumption).
    assert {{ Dom p ↦ ⇑ ℕ m ≈ p' ↦ ⇑ ℕ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    handle_per_univ_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: econstructor; eauto.
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
  intros * ? [env_relΓℕ] [].
  assert {{ Γ, ℕ ⊨ A : Type@i }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; econstructor; eassumption).
  assert {{ Γ ⊨ M : ℕ }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; econstructor; eassumption).
  destruct_conjs.
  pose (env_relΓℕ0 := env_relΓℕ).
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  assert {{ Dom p ↦ m0 ≈ p' ↦ m'0 ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; eauto).
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΓℕ) as [? []]).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; econstructor; only 1-2: repeat econstructor; eauto.
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
  unshelve eexists_rel_exp; [exact i |].
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
  enough (exists r r', {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} /\ {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ p' ↘ r' }} /\ elem_rel r r') by (destruct_conjs; econstructor; only 1-2: econstructor; eassumption).
  eapply eval_natrec_rel; try eassumption.
  destruct HAA' as [env_relΓℕ].
  assert {{ Γ, ℕ ⊨ A : Type@i }} as [] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; econstructor; eassumption).
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
  econstructor; eauto.
Qed.
