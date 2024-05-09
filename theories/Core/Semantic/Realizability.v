From Coq Require Import Lia PeanoNat Relation_Definitions.
From Equations Require Import Equations.
From Mcltt Require Import Base Evaluation LibTactics Readback.
From Mcltt Require Export PER.
Import Domain_Notations.

Lemma per_nat_then_per_top : forall {n m},
    {{ Dom n ≈ m ∈ per_nat }} ->
    {{ Dom ⇓ ℕ n ≈ ⇓ ℕ m ∈ per_top }}.
Proof with solve [eexists; firstorder (econstructor; eauto)].
  induction 1; simpl in *; intros s.
  - idtac...
  - specialize (IHper_nat s) as [? []]...
  - specialize (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_nat_then_per_top : mcltt.

Lemma realize_per_univ_elem_gen : forall {i a a' R},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}).
Proof with (solve [try (try (eexists; split); econstructor); mauto]).
  intros * H; simpl in H.
  induction H using per_univ_elem_ind; repeat split; intros.
  - subst...
  - eexists.
    per_univ_elem_econstructor...
  - destruct H2.
    specialize (H1 _ _ _ H2) as [? []].
    intro s.
    specialize (H1 s) as [? []]...
  - idtac...
  - idtac...
  - eauto using per_nat_then_per_top.
  - destruct IHper_univ_elem as [? []].
    intro s.
    assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H10 (S s)) as [? []].
    specialize (H3 s) as [? []]...
  - rewrite H2; clear H2.
    intros c0 c0' equiv_c0_c0'.
    destruct_all.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ A c0 ≈ c' ⇓ A' c0' ∈ per_bot }}) by eauto.
    intro s.
    specialize (H3 s) as [? []].
    specialize (H5 _ _ equiv_c0_c0' s) as [? []]...
  - rewrite H2 in *; clear H2.
    destruct_all.
    intro s.
    assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    assert {{ Dom ⇓ a fa ≈ ⇓ a' f'a' ∈ per_top }} by eauto.
    specialize (H2 s) as [? []].
    specialize (H16 (S s)) as [? []]...
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []])...
  - idtac...
  - intro s.
    (on_all_hyp: fun H => specialize (H s) as [? []]).
    (on_all_hyp: fun H => inversion_clear H; let n := numgoals in guard n <= 1).
    (on_all_hyp: fun H => specialize (H s) as [? []])...
Qed.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}.
Proof.
  intros.
  eapply realize_per_univ_elem_gen; eauto.
Qed.

#[export]
Hint Resolve per_univ_then_per_top_typ : mcltt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros.
  eapply realize_per_univ_elem_gen; eauto.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros.
  eapply realize_per_univ_elem_gen; eauto.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mcltt.
