From Coq Require Import Morphisms_Relations Relation_Definitions RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.TermStructureCases System.
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
  intros * equiv_Γ_Γ HAA' [] [env_relΓℕA] equiv_m_m'.
  assert {{ Γ, ℕ ⊨ A : Type@i }} as [env_relΓℕ] by (unfold valid_exp_under_ctx; etransitivity; [| symmetry]; eassumption).
  destruct_conjs.
  pose (env_relΓℕA0 := env_relΓℕA).
  pose (env_relΓℕ0 := env_relΓℕ).
  match_by_head (per_ctx_env env_relΓℕA) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  match_by_head (per_ctx_env env_relΓℕ) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  induction equiv_m_m'; intros;
    destruct_by_head rel_typ;
    (on_all_hyp: destruct_rel_by_assumption env_relΓ);
    invert_rel_typ_body;
    destruct_by_head rel_typ;
    dir_inversion_by_head eval_exp; subst;
    dir_inversion_by_head eval_sub; subst;
    dir_inversion_by_head eval_exp; subst;
    functional_eval_rewrite_clear;
    destruct_by_head rel_exp;
    handle_per_univ_elem_irrel.
  - do 2 eexists.
    repeat split; only 1-2: econstructor; eauto.
  - assert {{ Dom p'2 ↦ m ≈ p'3 ↦ n ∈ env_relΓℕ }} by (apply_relation_equivalence; eexists; eauto).
    (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
    assert {{ Dom p'2 ↦ m ≈ p'3 ↦ n ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    unshelve epose proof (IHequiv_m_m' _ _ equiv_p_p' _ _) as [? [? [? []]]]; [| econstructor; solve [eauto] |].
    handle_per_univ_elem_irrel.
    rename x4 into r0.
    rename x5 into r'0.
    assert {{ Dom p'2 ↦ m ↦ r0 ≈ p'3 ↦ n ↦ r'0 ∈ env_relΓℕA }} as HinΓℕA by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕA) as [? []]).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    dir_inversion_by_head eval_sub; subst.
    dir_inversion_by_head (eval_exp {{{ zero }}}); subst.
    dir_inversion_by_head (eval_exp {{{ succ #1 }}}); subst.
    dir_inversion_by_head (eval_exp {{{ #1 }}}); subst.
    match_by_head eval_exp ltac:(fun H => simpl in H).
    clear_refl_eqs.
Abort.

Lemma rel_exp_natrec_cong : forall {Γ MZ MZ' MS MS' A A' i M M'},
    {{ Γ, ℕ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊨ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊨ M ≈ M' : ℕ }} ->
    {{ Γ ⊨ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓℕ] [env_relΓ] [env_relΓℕA] [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΓℕ0 := env_relΓℕ).
  pose (env_relΓℕA0 := env_relΓℕA).
  inversion_by_head (per_ctx_env env_relΓℕA); subst.
  inversion_by_head (per_ctx_env env_relΓℕ); subst.
  handle_per_ctx_env_irrel.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption tail_rel0).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ ℕ }}}); subst.
  match goal with
  | H : per_univ_elem _ _ d{{{ ℕ }}} d{{{ ℕ }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence
  end.
  inversion_by_head (eval_exp {{{ A[Id ,, zero] }}}); subst.
  inversion_by_head (eval_sub {{{ Id ,, zero }}}); subst.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  match goal with
  | HM : {{ ⟦ M ⟧ p ↘ ~?m }}, HM' : {{ ⟦ M' ⟧ p' ↘ ~?m' }} |- _ =>
      assert {{ Dom p ↦ m ≈ p' ↦ m' ∈ env_relΓℕ }} as Hequiv by (apply_relation_equivalence; eexists; eauto)
  end.
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ Hequiv) as [? []]).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_by_head rel_exp.
  destruct_conjs.
  Abort.
