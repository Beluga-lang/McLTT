From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER.Definitions PER.CoreTactics.
Import Domain_Notations.

Add Parametric Morphism A : PER
    with signature (@relation_equivalence A) ==> iff as PER_morphism.
Proof.
  split; intros []; econstructor; unfold Symmetric, Transitive in *; intuition.
Qed.

Add Parametric Morphism R0 `(R0_morphism : Proper _ ((@relation_equivalence domain) ==> (@relation_equivalence domain)) R0) A p A' p' : (rel_mod_eval R0 A p A' p')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma per_bot_sym : forall m n,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_bot_sym : mcltt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcltt.

#[export]
Instance per_bot_PER : PER per_bot.
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot : forall {n},
    {{ Dom !n ≈ !n ∈ per_bot }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mcltt.

Lemma per_top_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_sym : mcltt.

Lemma per_top_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ l ∈ per_top }} ->
    {{ Dom m ≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mcltt.

#[export]
Instance per_top_PER : PER per_top.
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mcltt.

Lemma per_top_typ_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mcltt.

Lemma per_top_typ_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mcltt.

#[export]
Instance per_top_typ_PER : PER per_top_typ.
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.

Lemma per_nat_sym : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mcltt.

Lemma per_nat_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mcltt.

#[export]
Instance per_nat_PER : PER per_nat.
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
Qed.

Lemma per_ne_sym : forall m n,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mcltt.

Lemma per_ne_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mcltt.

#[export]
Instance per_ne_PER : PER per_ne.
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof with mautosolve.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    induction Horig using per_univ_elem_ind; basic_per_univ_elem_econstructor; eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor...
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> (@relation_equivalence domain) as per_univ_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros ** a b.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism i A p A' p' : (rel_typ i A p A' p')
    with signature (@relation_equivalence domain) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.

Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a ≈ b' ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof with (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear; econstructor; intuition).
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  induction Horig using per_univ_elem_ind; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros.
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder...
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder...
Qed.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ~?a ≈ ~?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~?a ≈ ~?b' ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Lemma per_univ_elem_sym : forall i R a b,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ a ∈ per_univ_elem i ↘ R }} /\
      (forall m m',
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Dom m' ≈ m ∈ R }}).
Proof with mautosolve.
  simpl.
  induction 1 using per_univ_elem_ind; subst;
    (* why does rewrite on <~> works only with this? *)
    pose proof (@relation_equivalence_pointwise domain).
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1...
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]...
  - destruct_conjs.
    split.
    + basic_per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; apply_relation_equivalence]...
Qed.

Corollary per_univ_sym : forall i R a b,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈ a ∈ per_univ_elem i ↘ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a' ≈ b ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b' ≈ a ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~_ ≈ ~?A ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      (* Order matters less here as H1 and H2 cannot be exchanged *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_univ_elem_trans : forall i R A1 A2,
    per_univ_elem i R A1 A2 ->
    (forall j A3,
        per_univ_elem j R A2 A3 ->
        per_univ_elem i R A1 A3) /\
      (forall a1 a2 a3,
          R a1 a2 ->
          R a2 a3 ->
          R a1 a3).
Proof with (basic_per_univ_elem_econstructor; mautosolve).
  pose proof (@relation_equivalence_pointwise domain).
  induction 1 using per_univ_elem_ind;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2; clear HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (* univ case *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    specialize (H3 _ _ _ H1) as [].
    eexists.
    intuition.
  - (* nat case *)
    idtac...
  - (* pi case *)
    destruct_conjs.
    basic_per_univ_elem_econstructor; eauto.
    + handle_per_univ_elem_irrel.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel...
  - (* fun case *)
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (* neut case *)
    idtac...
Qed.

Corollary per_univ_trans : forall i j R A1 A2 A3,
    per_univ_elem i R A1 A2 ->
    per_univ_elem j R A2 A3 ->
    per_univ_elem i R A1 A3.
Proof.
  intros * ?%per_univ_elem_trans.
  firstorder.
Qed.

Corollary per_elem_trans : forall i R A1 A2 a1 a2 a3,
    per_univ_elem i R A1 A2 ->
    R a1 a2 ->
    R a2 a3 ->
    R a1 a3.
Proof.
  intros * ?% per_univ_elem_trans.
  firstorder.
Qed.

#[export]
Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[export]
Instance per_elem_PER {i R A B} `(H : per_univ_elem i R A B) : PER R.
Proof.
  split.
  - eauto using (per_elem_sym _ _ _ _ _ _ H).
  - eauto using (per_elem_trans _ _ _ _ _ _ _ H).
Qed.

(* This lemma gets rid of the unnecessary PER premise. *)
Lemma per_univ_elem_pi' :
  forall i a a' p B p' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
    elem_rel,
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel}} ->
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem i ↘ elem_rel }}.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

#[export]
Hint Resolve per_univ_elem_pi' : mcltt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j a a' in_rel p p' B B' elem_rel},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
    {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem j ↘ elem_rel }} ->
    exists (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain),
      (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
          rel_mod_eval (per_univ_elem j) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) /\
        (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')).
Proof.
  intros * Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_typ j B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; [| eassumption | |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

Lemma per_univ_elem_cumu : forall i a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R }}.
Proof with solve [eauto].
  simpl.
  induction 1 using per_univ_elem_ind; subst;
    per_univ_elem_econstructor; eauto.
  intros.
  destruct_rel_mod_eval.
  econstructor...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu : mcltt.

Lemma per_univ_elem_cumu_ge : forall i i' a0 a1 R,
    i <= i' ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu_ge : mcltt.

Lemma per_univ_elem_cumu_max_left : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (i <= max i j) by lia...
Qed.

Lemma per_univ_elem_cumu_max_right : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem j ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (j <= max i j) by lia...
Qed.

Lemma per_subtyp_to_univ_elem : forall a b i,
    {{ Sub a <: b at i }} ->
    exists R R',
      {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} /\
        {{ DF b ≈ b ∈ per_univ_elem i ↘ R' }}.
Proof.
  destruct 1; do 2 eexists; mauto;
    split; per_univ_elem_econstructor; mauto;
    try apply Equivalence_Reflexive.
  lia.
Qed.

Lemma per_elem_subtyping : forall A B i,
    {{ Sub A <: B at i }} ->
    forall R R' a b,
      {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} ->
      {{ DF B ≈ B ∈ per_univ_elem i ↘ R' }} ->
      R a b ->
      R' a b.
Proof.
  induction 1; intros.
  4:clear H3 H4.
  all:(on_all_hyp: fun H => directed invert_per_univ_elem H);
    apply_equiv_left;
    trivial.
  - firstorder mauto.
  - intros.
    deepexec IHper_subtyp ltac:(fun H => pose proof H).
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    deepexec H1 ltac:(fun H => pose proof H).
    econstructor; eauto.
    repeat match goal with
           | H : per_univ_elem i _ ?x ?y |- _ =>
               tryif unify x y
               then fail
               else
                 assert (per_univ_elem i _ x x) by
               eauto using per_univ_sym, per_univ_trans;
               assert (per_univ_elem i _ y y) by
                 eauto using per_univ_sym, per_univ_trans;
               fail_if_dup
           end.
    deepexec H2 ltac:(fun H => pose proof H).
    trivial.
Qed.

Lemma PER_refl1 A (R : relation A) `(per : PER A R) : forall a b, R a b -> R a a.
Proof.
  intros.
  etransitivity; [eassumption |].
  symmetry. assumption.
Qed.

Lemma PER_refl2 A (R : relation A) `(per : PER A R) : forall a b, R a b -> R b b.
Proof.
  intros. symmetry in H.
  apply PER_refl1 in H;
    auto.
Qed.

Ltac saturate_refl :=
  repeat match goal with
    | H : ?R ?a ?b |- _ =>
        tryif unify a b
        then fail
        else
          directed pose proof (PER_refl1 _ _ _ _ _ H);
        directed pose proof (PER_refl2 _ _ _ _ _ H);
        fail_if_dup
    end.


Lemma per_subtyp_refl : forall a b i R,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub a <: b at i }} /\ {{ Sub b <: a at i }}.
Proof.
  simpl; induction 1 using per_univ_elem_ind;
    subst;
    mauto;
    destruct_all.

  assert ({{ DF Π A p B ≈ Π A' p' B' ∈ per_univ_elem i ↘ elem_rel }})
    by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto).
  saturate_refl.
  split; econstructor; eauto.
  - intros;
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
  - intros. symmetry in H12.
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub a <: b at i }}.
Proof.
  intros.
  apply per_subtyp_refl in H.
  firstorder.
Qed.

Lemma per_subtyp_refl2 : forall a b i R,
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub b <: a at i }}.
Proof.
  intros.
  apply per_subtyp_refl in H.
  firstorder.
Qed.

Inductive sub_trans_measure : domain -> Prop :=
| stm_neut : forall a b,
    sub_trans_measure d{{{ ⇑ a b }}}
| stm_nat :
  sub_trans_measure d{{{ ℕ }}}
| stm_univ : forall i,
    sub_trans_measure d{{{ 𝕌 @ i }}}
| stm_pi : forall a p B i in_rel,
    sub_trans_measure a ->
    {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
    (forall c b : domain,
        {{ Dom c ≈ c ∈ in_rel }} ->
        {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
        sub_trans_measure b) ->
    sub_trans_measure d{{{ Π a p B }}}.

#[local]
  Hint Constructors sub_trans_measure : mcltt.


Lemma sub_trans_measure_exists : forall A1 A2 i R,
    {{ DF A1 ≈ A2 ∈ per_univ_elem i ↘ R }} ->
    sub_trans_measure A1.
Proof.
  simpl. induction 1 using per_univ_elem_ind; mauto.
  saturate_refl.
  econstructor; mauto; intros.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  trivial.
Qed.

Lemma per_subtyp_trans' : forall A2,
    sub_trans_measure A2 ->
    forall A1 A3 i,
      {{ Sub A1 <: A2 at i }} ->
      {{ Sub A2 <: A3 at i }} ->
      {{ Sub A1 <: A3 at i }}.
Proof.
  induction 1; intros ? ? ? Hsub1 Hsub2; simpl in *.
  1-3:progressive_inversion;
  mauto.
  - econstructor; lia.
  - dependent destruction Hsub1.
    dependent destruction Hsub2.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intros.
    deepexec per_elem_subtyping ltac:(fun H => pose proof H).
    saturate_refl.
    directed invert_per_univ_elem H9.
    directed invert_per_univ_elem H10.
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    deepexec (H4 c c') ltac:(fun H => pose proof H).
    deepexec (H8 c' c') ltac:(fun H => pose proof H).
    eapply H2; apply_equiv_left; eauto.
Qed.

Lemma per_subtyp_trans : forall A1 A2 A3 i,
    {{ Sub A1 <: A2 at i }} ->
    {{ Sub A2 <: A3 at i }} ->
    {{ Sub A1 <: A3 at i }}.
Proof.
  intros.
  destruct (per_subtyp_to_univ_elem _ _ _ H0) as [? [? []]].
  eauto using per_subtyp_trans', sub_trans_measure_exists.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros p p'.
  split; intros [].
  - assert (equiv0_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel0 }}) by intuition...
  - assert (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel }}) by intuition...
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }} /\
      (forall o p,
          {{ Dom o ≈ p ∈ R }} ->
          {{ Dom p ≈ o ∈ R }}).
Proof with solve [intuition].
  simpl.
  induction 1; split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise env).
  - assert (tail_rel p' p) by eauto.
    assert (tail_rel p p) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_conjs.
    assert (tail_rel d{{{ p ↯ }}} d{{{ o ↯ }}}) by eauto.
    assert (tail_rel d{{{ p ↯ }}} d{{{ p ↯ }}}) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    eexists.
    handle_per_univ_elem_irrel; symmetry; intuition.
Qed.

Corollary per_ctx_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym : forall Γ Δ R o p,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ Dom o ≈ p ∈ R }} ->
    {{ Dom p ≈ o ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (* Order matters less here as H1 and H2 cannot be exchanged *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R }} ->
        {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R }}) /\
      (forall p1 p2 p3,
          {{ Dom p1 ≈ p2 ∈ R }} ->
          {{ Dom p2 ≈ p3 ∈ R }} ->
          {{ Dom p1 ≈ p3 ∈ R }}).
Proof with solve [eauto using per_univ_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise env);
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel p p) by intuition.
      assert (tail_rel0 p p') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      (* This one cannot be replaced with `etransitivity` as we need different `i`s. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - destruct_conjs.
    assert (tail_rel d{{{ p1 ↯ }}} d{{{ p3 ↯ }}}) by eauto.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    eexists.
    apply_relation_equivalence.
    etransitivity; intuition.
Qed.

Corollary per_ctx_trans : forall Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans : forall Γ1 Γ2 R p1 p2 p3,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ Dom p1 ≈ p2 ∈ R }} ->
    {{ Dom p2 ≈ p3 ∈ R }} ->
    {{ Dom p1 ≈ p3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[export]
Instance per_ctx_PER {R} : PER (per_ctx_env R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[export]
Instance per_env_PER {R Γ Δ} (H : per_ctx_env R Γ Δ) : PER R.
Proof.
  split.
  - auto using (per_env_sym _ _ _ _ _ H).
  - eauto using (per_env_trans _ _ _ _ _ _ H).
Qed.

(* This lemma removes the PER argument *)
Lemma per_ctx_env_cons' : forall {Γ Γ' i A A' tail_rel}
                             (head_rel : forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}), relation domain)
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }} ->
    (forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}),
        rel_typ i A p A' p' (head_rel equiv_p_p')) ->
    (env_rel <~> fun p p' =>
         exists (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel }}),
           {{ Dom ~(p 0) ≈ ~(p' 0) ∈ head_rel equiv_p_drop_p'_drop }}) ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mcltt.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_relΓA }} -> 
    exists i (head_rel : forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}), relation domain),
      (forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_relΓ }}),
          rel_typ i A p A' p' (head_rel equiv_p_p')) /\
        (env_relΓA <~> fun p p' =>
             exists (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ env_relΓ }}),
               {{ Dom ~(p 0) ≈ ~(p' 0) ∈ head_rel equiv_p_drop_p'_drop }}).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; intros.
  - instantiate (1 := fun p p' (equiv_p_p' : env_relΓ p p') m m' =>
                        forall R,
                          rel_typ i A p A' p' R ->
                          {{ Dom m ≈ m' ∈ R }}).
    assert (tail_rel p p') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
  - intros o o'.
    split; intros; destruct_conjs;
      assert {{ Dom o ↯ ≈ o' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve eexists; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
Qed.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; destruct H as [? [? []]])
  + (inversion H; subst).

Lemma per_ctx_respects_length : forall {Γ Γ'},
    {{ Exp Γ ≈ Γ' ∈ per_ctx }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.
