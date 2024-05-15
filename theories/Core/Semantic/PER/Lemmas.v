From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mcltt Require Import Axioms Base Evaluation LibTactics PER.Definitions Readback.
Import Domain_Notations.

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

Lemma per_univ_elem_respect_iff : forall i R a a' R',
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    (forall m m', {{ Dom m ≈ m' ∈ R }} <-> {{ Dom m ≈ m' ∈ R' }}) ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R' }}.
Proof with mautosolve.
  simpl.
  intros * Horig. gen R'.
  induction Horig using per_univ_elem_ind; per_univ_elem_econstructor; mauto;
    intros;
    intuition.
  destruct_rel_mod_eval.
  econstructor...
Qed.

#[export]
Hint Resolve per_univ_elem_respect_iff : mcltt.

Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a ≈ b' ∈ per_univ_elem i' ↘ R' }} ->
    (forall m m', {{ Dom m ≈ m' ∈ R }} <-> {{ Dom m ≈ m' ∈ R' }}).
Proof with mautosolve.
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  induction Horig using per_univ_elem_ind; intros * Heq Hright;
    subst; invert_per_univ_elem Hright; unfold per_univ;
    intros;
    (on_all_hyp: fun H => rewrite H; let n := numgoals in guard n <= 1);
    firstorder;
    specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    econstructor; eauto.
    intuition.
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    econstructor; eauto.
    intuition.
Qed.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ~?a ≈ ~?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~?a ≈ ~?b' ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      assert (forall m m', R1 m m' <-> R2 m m') by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]);
      let H := fresh "H" in
      assert (forall m m', R2 m m' <-> R1 m m') by (eapply per_univ_elem_right_irrel; [apply H2 | apply H1]);
      fail_if_dup;
      clear H
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
  induction 1 using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros. rewrite H1 in *. destruct H0. eexists. eapply proj1, H2...
  - split; [econstructor | intros; rewrite H in *]...
  - destruct_conjs.
    split.
    + per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; mauto.
      eapply per_univ_elem_respect_iff; mauto.
      intros.
      per_univ_elem_right_irrel_assert.
      intuition.
    + (on_all_hyp: fun H => setoid_rewrite H).
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; mauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; rewrite H0 in *]...
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
    (forall m m', {{ Dom m ≈ m' ∈ R }} <-> {{ Dom m ≈ m' ∈ R' }}).
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    {{ DF a ≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b' ≈ a ∈ per_univ_elem i' ↘ R' }} ->
    (forall m m', {{ Dom m ≈ m' ∈ R }} <-> {{ Dom m ≈ m' ∈ R' }}).
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
      assert (forall m m', R1 m m' <-> R2 m m') by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2;
      let H := fresh "H" in
      assert (forall m m', R2 m m' <-> R1 m m') by (eapply per_univ_elem_right_irrel; [apply H2 | apply H1]) || tactic_error R2 R1;
      fail_if_dup;
      clear H
  | H1 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      assert (forall m m', R1 m m' <-> R2 m m') by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2;
      let H := fresh "H" in
      assert (forall m m', R2 m m' <-> R1 m m') by (eapply per_univ_elem_left_irrel; [apply H2 | apply H1]) || tactic_error R2 R1;
      fail_if_dup;
      clear H
  | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ~_ ≈ ~?A ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      (* Order matters less here as H1 and H2 cannot be exchanged *)
      assert_fails (unify R1 R2);
      assert (forall m m', R1 m m' <-> R2 m m') by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2;
      let H := fresh "H" in
      assert (forall m m', R2 m m' <-> R1 m m') by (intros; intuition) || tactic_error R2 R1;
      fail_if_dup;
      clear H
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
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
Proof with (try (econstructor + per_univ_elem_econstructor); mautosolve).
  induction 1 using per_univ_elem_ind;
    [> split;
     [ intros * HT2; invert_per_univ_elem HT2; clear HT2
     | intros * HTR1 HTR2; (on_all_hyp: fun H => apply H; apply H in HTR1, HTR2) ] ..]; mauto.
  - (* univ case *)
    destruct HTR1, HTR2.
    handle_per_univ_elem_irrel.
    specialize (H2 _ _ _ H3) as [].
    (on_all_hyp: fun H => eapply per_univ_elem_respect_iff in H; intuition)...
  - (* nat case *)
    idtac...
  - (* pi case *)
    destruct_conjs.
    per_univ_elem_econstructor; eauto.
    + (on_all_hyp: fun H => eapply per_univ_elem_respect_iff in H; intuition; let n := numgoals in guard n <= 1).
      handle_per_univ_elem_irrel.
      eapply per_univ_elem_respect_iff; mauto.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel.
      econstructor; eauto.
      eapply per_univ_elem_respect_iff; mauto.
      intuition.
  - (* fun case *)
    apply H2.
    rewrite -> H2 in HTR1, HTR2.
    intros.
    assert (in_rel c c) by (etransitivity; [ | symmetry]; eassumption).
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
Instance per_elem_PER {i R A B} `(H : per_univ_elem i R A B) : PER R.
Proof.
  split.
  - eauto using (per_elem_sym _ _ _ _ _ _ H).
  - eauto using (per_elem_trans _ _ _ _ _ _ _ H).
Qed.


#[export]
Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

(* This lemma gets rid of the unnecessary PER premise. *)
Lemma per_univ_elem_core_pi' :
  forall i A p B A' p' B' elem_rel
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
    (equiv_a_a' : {{ DF A ≈ A' ∈ per_univ_elem i ↘ in_rel}}),
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
    (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app (out_rel equiv_c_c') f c f' c') ->
    {{ DF Π A p B ≈ Π A' p' B' ∈ per_univ_elem i ↘ elem_rel }}.
Proof.
  intros.
  per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

Lemma per_univ_elem_cumu : forall i a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R }}.
Proof with solve [eauto].
  simpl.
  induction 1 using per_univ_elem_ind; subst.
  - eapply per_univ_elem_core_univ'...
  - per_univ_elem_econstructor...
  - per_univ_elem_econstructor; mauto.
    intros.
    destruct_rel_mod_eval.
    econstructor...
  - per_univ_elem_econstructor...
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R <-> R'.
Proof.
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst; try congruence.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  subst.
  enough (head_rel = head_rel0) by now subst.
  extensionality p.
  extensionality p'.
  extensionality equiv_p_p'.
  simpl in *.
  destruct_rel_mod_eval.
  per_univ_elem_irrel_rewrite.
  congruence.
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }} /\
      (forall o p,
          {{ Dom o ≈ p ∈ R }} ->
          {{ Dom p ≈ o ∈ R }}).
Proof with solve [eauto using per_univ_sym].
  simpl.
  induction 1; split; try solve [econstructor; eauto]; simpl in *; destruct_conjs.
  - econstructor; eauto.
    intros.
    assert (tail_rel p' p) by eauto.
    assert (tail_rel p p) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite.
    econstructor...
  - subst.
    intros.
    destruct_conjs.
    assert (tail_rel d{{{ p ↯ }}} d{{{ o ↯ }}}) by eauto.
    assert (tail_rel d{{{ p ↯ }}} d{{{ p ↯ }}}) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    eexists.
    per_univ_elem_irrel_rewrite.
    eapply per_elem_sym...
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
    R = R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_rewrite1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by first [solve [eauto using per_ctx_env_right_irrel] | tactic_error R2 R1]
    | H1 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by first [solve [eauto using per_ctx_env_left_irrel] | tactic_error R2 R1]
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (* Order matters less here as H1 and H2 cannot be exchanged *)
        clean replace R2 with R1 by first [solve [symmetry; eauto using per_ctx_env_cross_irrel] | tactic_error R2 R1]
    end.

Ltac do_per_ctx_env_irrel_rewrite :=
  repeat do_per_ctx_env_irrel_rewrite1.

Ltac per_ctx_env_irrel_rewrite :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_rewrite;
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
     | intros; destruct_conjs; unfold per_total; eauto] ..];
    per_ctx_env_irrel_rewrite.
  - rename tail_rel0 into tail_rel.
    econstructor; eauto.
    + eapply IHper_ctx_env...
    + intros.
      assert (tail_rel p p) by (etransitivity; [| symmetry]; eauto).
      (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
      per_univ_elem_irrel_rewrite.
      econstructor...
  - assert (tail_rel d{{{ p1 ↯ }}} d{{{ p3 ↯ }}}) by mauto.
    eexists.
    (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
    per_univ_elem_irrel_rewrite.
    eapply per_elem_trans...
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
