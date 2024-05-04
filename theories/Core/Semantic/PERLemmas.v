From Coq Require Import Lia PeanoNat Relations.Relation_Definitions RelationClasses Program.Equality.
From Equations Require Import Equations.
From Mcltt Require Import Axioms Base Domain Evaluate EvaluateLemmas LibTactics PER Readback ReadbackLemmas Syntax System.

Lemma per_bot_sym : forall m n,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [mauto].
  intros * H s.
  destruct (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_bot_sym : mcltt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [mauto].
  intros * Hmn Hnl s.
  destruct (Hmn s) as [? []].
  destruct (Hnl s) as [? []].
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcltt.

Lemma per_nat_sym : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof with solve [mauto].
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mcltt.

Lemma per_nat_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof with solve [mauto].
  intros * H. gen l.
  induction H; intros * H'; inversion_clear H'; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mcltt.

Lemma per_ne_sym : forall m n,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof with solve [mauto].
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mcltt.

Lemma per_ne_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with solve [mauto].
  intros * [] Hnl.
  inversion_clear Hnl.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mcltt.

Ltac invert_per_univ_elem H :=
  simp per_univ_elem in H;
  inversion H;
  subst;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac per_univ_elem_econstructor :=
  simp per_univ_elem;
  econstructor;
  try rewrite <- per_univ_elem_equation_1 in *.

Lemma per_univ_elem_right_irrel_gen : forall i A B R,
    per_univ_elem i A B R ->
    forall A' B' R',
      A = A' ->
      per_univ_elem i A' B' R' ->
      R = R'.
Proof.
  induction 1 using per_univ_elem_ind; intros * Heq Hright;
    try solve [induction Hright using per_univ_elem_ind; congruence].
  subst.
  invert_per_univ_elem Hright; try congruence.
  specialize (IHper_univ_elem _ _ _ eq_refl equiv_a_a').
  subst.
  extensionality f.
  extensionality f'.
  rewrite H2, H10.
  extensionality c.
  extensionality c'.
  extensionality equiv_c_c'.
  specialize (H1 _ _ equiv_c_c') as [? ? ? ? []].
  specialize (H9 _ _ equiv_c_c') as [? ? ? ? ?].
  functional_eval_rewrite_clear.
  specialize (H5 _ _ _ eq_refl H9).
  congruence.
Qed.

Lemma per_univ_elem_right_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i A B' R' ->
    R = R'.
Proof.
  intros. eauto using per_univ_elem_right_irrel_gen.
Qed.

Ltac per_univ_elem_right_irrel_rewrite :=
  repeat match goal with
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B' ∈ per_univ_elem ?i ↘ ?R1 }} |- _ =>
        mark H2
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B' ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        assert (R2 = R1) by (eapply per_univ_elem_right_irrel; eassumption); subst; mark H2
    end; unmark_all.

Ltac functional_per_univ_elem_rewrite_clear :=
  repeat match goal with
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }} |- _ =>
        clear H2
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        assert (R2 = R1) by (eapply per_univ_elem_right_irrel; eassumption); subst; clear H2
    end.

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    per_univ_elem i B A R /\ (forall a b, {{ Dom a ≈ b ∈ R }} <-> {{ Dom b ≈ a ∈ R }}).
Proof.
  intros. induction H using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; trivial.
    + intros. split; intros HD; destruct HD.
      * specialize (H1 _ _ _ H0).
        firstorder.
      * specialize (H1 _ _ _ H0).
        firstorder.
  - split.
    + econstructor.
    + intros; split; mauto.
  - destruct IHper_univ_elem as [? ?].
    setoid_rewrite H2.
    split.
    + per_univ_elem_econstructor; eauto.
      intros.
      assert (equiv_c'_c : in_rel c' c) by firstorder.
      assert (equiv_c_c : in_rel c c) by (etransitivity; eassumption).
      destruct (H1 _ _ equiv_c_c') as [? ? ? ? [? [? ?]]].
      destruct (H1 _ _ equiv_c'_c) as [? ? ? ? [? [? ?]]].
      destruct (H1 _ _ equiv_c_c) as [? ? ? ? [? [? ?]]].
      econstructor; eauto.
      functional_eval_rewrite_clear.
      per_univ_elem_right_irrel_rewrite.
      congruence.

    + assert (forall a b : domain,
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') a c b c') ->
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') b c a c')). {
        intros.
        assert (equiv_c'_c : in_rel c' c) by firstorder.
        assert (equiv_c_c : in_rel c c) by (etransitivity; eassumption).
        destruct (H1 _ _ equiv_c_c') as [? ? ? ? [? [? ?]]].
        destruct (H1 _ _ equiv_c'_c) as [? ? ? ? [? [? ?]]].
        destruct (H1 _ _ equiv_c_c) as [? ? ? ? [? [? ?]]].
        destruct (H5 _ _ equiv_c'_c) as [? ? ? ? ?].
        functional_eval_rewrite_clear.
        per_univ_elem_right_irrel_rewrite.
        econstructor; eauto.
        rewrite H17, H16.
        firstorder.
      }
      firstorder.
  - split.
    + econstructor.
    + intros; split; mauto.
Qed.

Lemma per_univ_elem_left_irrel : forall i A B R A' R',
    per_univ_elem i A B R ->
    per_univ_elem i A' B R' ->
    R = R'.
Proof.
  intros.
  apply per_univ_elem_sym in H.
  apply per_univ_elem_sym in H0.
  destruct_all.
  eauto using per_univ_elem_right_irrel.
Qed.

Lemma per_univ_elem_cross_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i B' A R' ->
    R = R'.
Proof.
  intros.
  apply per_univ_elem_sym in H0.
  destruct_all.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_rewrite1 :=
  match goal with
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        tryif unify R1 R2 then fail else
          (let H := fresh "H" in assert (R1 = R2) as H by (eapply per_univ_elem_right_irrel; eassumption); subst;
                                 try rewrite <- H in *)
    | H1 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        tryif unify R1 R2 then fail else
          (let H := fresh "H" in assert (R1 = R2) as H by (eapply per_univ_elem_left_irrel; eassumption); subst;
                                 try rewrite <- H in *)
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?A ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        tryif unify R1 R2 then fail else
          (let H := fresh "H" in assert (R1 = R2) as H by (eapply per_univ_elem_cross_irrel; eassumption); subst;
                                 try rewrite <- H in *)
    end.

Ltac do_per_univ_elem_irrel_rewrite :=
  repeat do_per_univ_elem_irrel_rewrite1.

Ltac per_univ_elem_irrel_rewrite :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_rewrite;
  clear_dups.

Lemma per_univ_elem_trans : forall i A1 A2 R,
    per_univ_elem i A1 A2 R ->
    forall A3,
    per_univ_elem i A2 A3 R ->
    per_univ_elem i A1 A3 R /\ (forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3).
Proof with solve [mauto].
  induction 1 using per_univ_elem_ind; intros * HT2;
    invert_per_univ_elem HT2; clear HT2.
  - split; mauto.
    intros.
    destruct H0, H2.
    per_univ_elem_irrel_rewrite.
    destruct (H1 _ _ _ H0 _ H2) as [? ?].
    econstructor...
  - split; try econstructor...
  - per_univ_elem_irrel_rewrite.
    specialize (IHper_univ_elem _ equiv_a_a') as [? _].
    split.
    + per_univ_elem_econstructor; mauto.
      intros.
      assert (equiv_c_c : in_rel c c) by (etransitivity; [ | symmetry]; eassumption).
      specialize (H1 _ _ equiv_c_c) as [? ? ? ? [? ?]].
      specialize (H9 _ _ equiv_c_c') as [].
      per_univ_elem_irrel_rewrite.
      firstorder (econstructor; eauto).
    + setoid_rewrite H2.
      intros.
      assert (equiv_c'_c' : in_rel c' c') by (etransitivity; [symmetry | ]; eassumption).
      destruct (H1 _ _ equiv_c_c') as [? ? ? ? [? ?]].
      specialize (H1 _ _ equiv_c'_c') as [? ? ? ? [? ?]].
      specialize (H9 _ _ equiv_c'_c') as [].
      specialize (H3 _ _ equiv_c_c') as [].
      specialize (H4 _ _ equiv_c'_c') as [].
      per_univ_elem_irrel_rewrite.
      firstorder (econstructor; eauto).

  - split; try per_univ_elem_econstructor...
Qed.
