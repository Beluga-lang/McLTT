From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export Evaluation NbE PER Readback.
Import Domain_Notations.

Lemma per_nat_then_per_top : forall {n m},
    {{ Dom n ≈ m ∈ per_nat }} ->
    {{ Dom ⇓ ℕ n ≈ ⇓ ℕ m ∈ per_top }}.
Proof with solve [destruct_conjs; eexists; repeat econstructor; eauto].
  induction 1; simpl in *; intros s;
    try specialize (IHper_nat s);
    try specialize (H s)...
Qed.

#[export]
Hint Resolve per_nat_then_per_top : mcltt.

Lemma realize_per_univ_elem_gen : forall {i a a' R},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}).
Proof with (solve [try (try (eexists; split); econstructor); mauto]).
  pose proof (@relation_equivalence_pointwise domain).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - subst.
    eexists.
    per_univ_elem_econstructor...
  - subst.
    destruct_by_head per_univ.
    specialize (H3 _ _ _ H1).
    destruct_conjs.
    intro s.
    specialize (H2 s) as [? []]...
  - destruct IHHunivelem as [? []].
    intro s.
    assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H10 (S s)) as [? []].
    specialize (H3 s) as [? []]...
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ A c0 ≈ c' ⇓ A' c0' ∈ per_bot }}) by eauto.
    intro s.
    specialize (H4 s) as [? []].
    specialize (H6 _ _ equiv_c0_c0' s) as [? []]...
  - destruct_conjs.
    intro s.
    assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    assert {{ Dom ⇓ a fa ≈ ⇓ a' f'a' ∈ per_top }} by eauto.
    specialize (H3 s) as [? []].
    specialize (H17 (S s)) as [? []]...
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []])...
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []])...
Qed.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_univ_then_per_top_typ : mcltt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mcltt.

Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_rel }} ->
    exists p p', initial_env Γ p /\ initial_env Γ' p' /\ {{ Dom p ≈ p' ∈ env_rel }}.
Proof.
  pose proof (@relation_equivalence_pointwise env).
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
Qed.
