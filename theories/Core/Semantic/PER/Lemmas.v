From Coq Require Import Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mcltt Require Import Axioms Base LibTactics.
From Mcltt.Core Require Import Evaluation PER.Definitions PER.CoreTactics Readback.
Import Domain_Notations.

Add Parametric Morphism A : (@all A)
    with signature forall_relation (fun (x : A) => iff) ==> iff as all_iff_moprhism'.
Proof.
  unfold forall_relation.
  split; intros ** ?; intuition.
Qed.

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

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof with mautosolve.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    induction Horig using per_univ_elem_ind; per_univ_elem_econstructor; eauto;
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
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence := rewrite_relation_equivalence_right; clear_relation_equivalence; rewrite_relation_equivalence_left; clear_relation_equivalence.

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
    subst; invert_per_univ_elem Hright; unfold per_univ;
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
  - split; [per_univ_elem_econstructor | intros; apply_relation_equivalence]...
  - destruct_conjs.
    split.
    + per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; mauto.
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
      econstructor; mauto.
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
Proof with (per_univ_elem_econstructor; mautosolve).
  pose proof (@relation_equivalence_pointwise domain).
  induction 1 using per_univ_elem_ind;
    [> split;
     [ intros * HT2; invert_per_univ_elem HT2; clear HT2
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
    per_univ_elem_econstructor; eauto.
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
Lemma per_univ_elem_core_pi' :
  forall i A p B A' p' B' elem_rel
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
    (equiv_a_a' : {{ DF A ≈ A' ∈ per_univ_elem i ↘ in_rel}}),
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
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

Lemma per_univ_elem_cumu_ge : forall i i' a0 a1 R,
    i <= i' ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem i' ↘ R }}.
Proof with solve [eauto using per_univ_elem_cumu].
  induction 1...
Qed.

Lemma per_univ_elem_cumu_max_left : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with solve [eauto using per_univ_elem_cumu_ge].
  intros.
  assert (i <= max i j) by lia...
Qed.

Lemma per_univ_elem_cumu_max_right : forall i j a0 a1 R,
    {{ DF a0 ≈ a1 ∈ per_univ_elem j ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with solve [eauto using per_univ_elem_cumu_ge].
  intros.
  assert (j <= max i j) by lia...
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
Proof with mautosolve.
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
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved by mauto" in
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
