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

Lemma iff_extensionality : forall (A : Type) (Q P : A -> Prop),
    (forall a, P a <-> Q a) ->
    (forall a, P a) <-> (forall a, Q a).
Proof.
  firstorder.
Qed.

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

    + split; intros.
      * assert (equiv_c'_c : in_rel c' c) by firstorder.
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

      * assert (equiv_c'_c : in_rel c' c) by firstorder.
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

(* JH: the code below has not been fixed yet *)

Ltac per_univ_elem_left_irrel_rewrite :=
  repeat match goal with
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A' ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }} |- _ =>
        mark H2
    | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A' ≈ ~?B ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        assert (R2 = R1) by (eapply per_univ_elem_left_irrel; eassumption); subst; mark H2
    end; unmark_all.

Ltac per_univ_elem_irrel_rewrite := functional_per_univ_elem_rewrite_clear; per_univ_elem_right_irrel_rewrite; per_univ_elem_left_irrel_rewrite.

Lemma per_univ_elem_trans : forall i A1 A2 R1,
    per_univ_elem i A1 A2 R1 ->
    forall A3 R2,
    per_univ_elem i A2 A3 R2 ->
    exists R3, per_univ_elem i A1 A3 R3 /\ (forall a1 a2 a3, R1 a1 a2 -> R2 a2 a3 -> R3 a1 a3).
Proof with solve [mauto].
  induction 1 using per_univ_elem_ind; intros * HT2;
    invert_per_univ_elem HT2; clear HT2.
  - exists (per_univ j'0).
    split; mauto.
    intros.
    destruct H0, H2.
    destruct (H1 _ _ _ H0 _ _ H2) as [? [? ?]].
    econstructor...
  - exists per_nat.
    split; try econstructor...
  - rename R2 into elem_rel0.
    destruct (IHper_univ_elem _ _ equiv_a_a') as [in_rel3 [? in_rel_trans]].
    per_univ_elem_irrel_rewrite.
    pose proof (per_univ_elem_sym _ _ _ _ H) as [in_rel' [? in_rel_sym]].
    specialize (IHper_univ_elem _ _ H3) as [in_rel'' [? _]].
    per_univ_elem_irrel_rewrite.
    rename in_rel0 into in_rel.
    assert (in_rel_refl : forall c c', in_rel c c' -> in_rel c' c').
    {
      intros.
      assert (equiv_c'_c : in_rel c' c) by (destruct in_rel_sym with c c'; mauto)...
    }
    assert (forall (c c' : domain) (equiv_c_c' : in_rel c c'),
             exists R3,
               rel_mod_eval
                 (fun (x y : domain) (R : relation domain) =>
                    per_univ_elem i x y R)
                 B d{{{ p ↦ c }}} B'0 d{{{ p'0 ↦ c' }}} R3
               /\ (forall c'' (equiv_c_c'' : in_rel c c'') (equiv_c''_c' : in_rel c'' c') b0 b1 b2,
                      out_rel _ _ equiv_c_c'' b0 b1 -> out_rel0 _ _ equiv_c''_c' b1 b2 -> R3 b0 b2)).
    {
      intros.
      assert (equiv_c'_c' : in_rel c' c') by mauto.
      destruct (H0 _ _ equiv_c_c') as [? ? ? ? []].
      destruct (H7 _ _ equiv_c'_c') as [].
      functional_eval_rewrite_clear.
      destruct (H10 _ _ H13) as [R []].
      exists R.
      split.
      - econstructor...
      - intros.
        specialize (H0 _ _ equiv_c_c'') as [? ? ? ? []].
        specialize (H7 _ _ equiv_c''_c') as [].
        functional_eval_rewrite_clear.
        specialize (H19 _ _ H21) as [R' []].
        per_univ_elem_irrel_rewrite.
        eapply H7...
    }
    repeat setoid_rewrite dep_functional_choice_equiv in H5.
    destruct H5 as [out_rel3 ?].
    exists (fun f f' => forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel3 c c' equiv_c_c') f c f' c').
    split.
    + per_univ_elem_econstructor; mauto.
      intros.
      specialize (H5 _ _ equiv_c_c') as []...
    + intros.
      assert (equiv_c'_c' : in_rel c' c') by mauto.
      rewrite H1 in H6.
      rewrite H8 in H9.
      specialize (H6 _ _ equiv_c_c') as [].
      specialize (H9 _ _ equiv_c'_c') as [].
      functional_eval_rewrite_clear.
      specialize (H5 _ _ equiv_c_c') as [].
      econstructor...
  - exists per_ne.
    split; try per_univ_elem_econstructor...
Qed.
