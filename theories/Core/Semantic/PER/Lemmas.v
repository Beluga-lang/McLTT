From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Mcltt Require Import Axioms Base Evaluation LibTactics PER.Definitions Readback.
Import Domain_Notations.

Lemma per_bot_sym : forall m n,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H s.
  destruct (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_bot_sym : mcltt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  destruct (Hmn s) as [? []].
  destruct (Hnl s) as [? []].
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcltt.

Lemma var_per_bot : forall {n},
    {{ Dom !n ≈ !n ∈ per_bot }}.
Proof.
  intros n s. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mcltt.

Lemma per_top_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H s.
  destruct (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_top_sym : mcltt.

Lemma per_top_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ l ∈ per_top }} ->
    {{ Dom m ≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  destruct (Hmn s) as [? []].
  destruct (Hnl s) as [? []].
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mcltt.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H s.
  specialize (H s) as [? []].
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mcltt.

Lemma per_top_typ_sym : forall m n,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H s.
  destruct (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mcltt.

Lemma per_top_typ_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  destruct (Hmn s) as [? []].
  destruct (Hnl s) as [? []].
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mcltt.

Lemma PER_per_top_typ : PER per_top_typ.
Proof with solve [mauto].
  econstructor...
Qed.

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

Lemma per_univ_elem_right_irrel : forall i i' A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i' A B' R' ->
    R = R'.
Proof.
  intros * Horig.
  remember A as A' in |- *.
  gen A' B' R'.
  induction Horig using per_univ_elem_ind; intros * Heq Hright;
    try solve [induction Hright using per_univ_elem_ind; congruence].
  subst.
  invert_per_univ_elem Hright; try congruence.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  subst.
  extensionality f.
  extensionality f'.
  rewrite H2, H10.
  extensionality c.
  extensionality c'.
  extensionality equiv_c_c'.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  specialize (H12 _ _ _ eq_refl H5).
  congruence.
Qed.

Ltac per_univ_elem_right_irrel_rewrite1 :=
  match goal with
  | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B' ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
      clean replace R2 with R1 by (eauto using per_univ_elem_right_irrel)
  end.
Ltac per_univ_elem_right_irrel_rewrite := repeat per_univ_elem_right_irrel_rewrite1.  

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    per_univ_elem i B A R /\ (forall a b, {{ Dom a ≈ b ∈ R }} -> {{ Dom b ≈ a ∈ R }}).
Proof with solve [try econstructor; mauto].
  induction 1 using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'...
    + intros * [].
      specialize (H1 _ _ _ H0) as []...
  - split...
  - destruct IHper_univ_elem as [? ?].
    setoid_rewrite H2.
    split.
    + per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by firstorder.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      per_univ_elem_right_irrel_rewrite...
    + enough (forall a b : domain,
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') a c b c') ->
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') b c a c')) by firstorder.
      intros.
      assert (in_rel c' c) by firstorder.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      per_univ_elem_right_irrel_rewrite...
  - split...
Qed.

Corollary per_univ_sym : forall i A B R,
    per_univ_elem i A B R ->
    per_univ_elem i B A R.
Proof.
  intros * HS.
  apply per_univ_elem_sym; assumption.
Qed.

Corollary per_elem_sym : forall i A B a b R,
    per_univ_elem i A B R ->
    R a b -> R b a.
Proof.
  intros * HS.
  eapply per_univ_elem_sym; eassumption.
Qed.

Lemma per_univ_elem_left_irrel : forall i i' A B R A' R',
    per_univ_elem i A B R ->
    per_univ_elem i' A' B R' ->
    R = R'.
Proof.
  intros * []%per_univ_elem_sym []%per_univ_elem_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Lemma per_univ_elem_cross_irrel : forall i i' A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i' B' A R' ->
    R = R'.
Proof.
  intros * ? []%per_univ_elem_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_rewrite1 :=
  match goal with
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_univ_elem_right_irrel)
    | H1 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_univ_elem_left_irrel)
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?A ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
        (* Order matters less here as H1 and H2 cannot be exchanged *)
        clean replace R2 with R1 by (symmetry; eauto using per_univ_elem_cross_irrel)
    end.

Ltac do_per_univ_elem_irrel_rewrite :=
  repeat do_per_univ_elem_irrel_rewrite1.

Ltac per_univ_elem_irrel_rewrite :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_rewrite;
  clear_dups.

Lemma per_univ_elem_trans : forall i A1 A2 R,
    per_univ_elem i A1 A2 R ->
    (forall j A3,
        per_univ_elem j A2 A3 R ->
        per_univ_elem i A1 A3 R) /\
      (forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3).
Proof with solve [mauto| firstorder (econstructor; eauto)].
  induction 1 using per_univ_elem_ind;
    [> split;
       [ intros * HT2; invert_per_univ_elem HT2; clear HT2
       | intros * HTR1 HTR2 ] ..]; mauto.
  - destruct HTR1, HTR2.
    per_univ_elem_irrel_rewrite.
    specialize (H1 _ _ _ H2) as [].
    specialize (H0 _ _ H3)...
  - idtac...
  - per_univ_elem_irrel_rewrite.
    rename in_rel0 into in_rel.
    destruct IHper_univ_elem as [? _].
    per_univ_elem_econstructor; mauto.
    intros.
    assert (in_rel c c) by (etransitivity; [ | symmetry]; eassumption).
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite...
  - destruct IHper_univ_elem as [? ?].
    rewrite H2 in *.
    intros.
    assert (in_rel c' c') by (etransitivity; [symmetry | ]; eassumption).
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    per_univ_elem_irrel_rewrite...
  - try per_univ_elem_econstructor...
Qed.

Corollary per_univ_trans : forall i j A1 A2 A3 R,
    per_univ_elem i A1 A2 R ->
    per_univ_elem j A2 A3 R ->
    per_univ_elem i A1 A3 R.
Proof.
  intros * HT1.
  apply per_univ_elem_trans; assumption.
Qed.

Corollary per_elem_trans : forall i A1 A2 a1 a2 a3 R,
    per_univ_elem i A1 A2 R ->
    R a1 a2 -> R a2 a3 -> R a1 a3.
Proof.
  intros * HT1.
  eapply per_univ_elem_trans; eassumption.
Qed.

Lemma per_univ_elem_cumu : forall {i a0 a1 R},
    {{ DF a0 ≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈ a1 ∈ per_univ_elem (S i) ↘ R }}.
Proof with solve [mauto].
  simpl.
  induction 1 using per_univ_elem_ind; subst.
  - eapply per_univ_elem_core_univ'.
    lia.
  - per_univ_elem_econstructor.
  - per_univ_elem_econstructor; mauto.
    intros.
    destruct_rel_mod_eval.
    econstructor...
  - per_univ_elem_econstructor...
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    try solve [inversion Hright; congruence].
  subst.
  inversion_clear Hright.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  subst.
  enough (head_rel = head_rel0) by (subst; easy).
  extensionality p.
  extensionality p'.
  extensionality equiv_p_p'.
  unfold rel_typ in *.
  destruct_rel_mod_eval.
  per_univ_elem_irrel_rewrite.
  congruence.
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env ↘ R }} /\ (forall o p, {{ Dom o ≈ p ∈ R }} -> {{ Dom p ≈ o ∈ R }}).
Proof with solve [eauto].
  simpl.
  induction 1; firstorder; try solve [econstructor; eauto]; unfold rel_typ in *.
  - econstructor; eauto; firstorder.
    assert (tail_rel p' p) by eauto.
    assert (tail_rel p p) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite.
    econstructor; eauto.
    apply per_univ_sym...
  - subst.
    firstorder.
    assert (tail_rel d{{{ p ↯ }}} d{{{ o ↯ }}}) by (unfold Symmetric in *; eauto).
    assert (tail_rel d{{{ p ↯ }}} d{{{ p ↯ }}}) by (etransitivity; eauto).
    destruct_rel_mod_eval.
    eexists.
    per_univ_elem_irrel_rewrite.
    eapply per_elem_sym...
Qed.

Lemma per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ' ≈ Δ ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * []%per_ctx_env_sym []%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Lemma per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R = R'.
Proof.
  intros * ? []%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_rewrite1 :=
  match goal with
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_ctx_env_right_irrel)
    | H1 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_ctx_env_left_irrel)
    | H1 : {{ DF ~?Γ ≈ ~_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (* Order matters less here as H1 and H2 cannot be exchanged *)
        clean replace R2 with R1 by (symmetry; eauto using per_ctx_env_cross_irrel)
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
      (forall p1 p2 p3, {{ Dom p1 ≈ p2 ∈ R }} -> {{ Dom p2 ≈ p3 ∈ R }} -> {{ Dom p1 ≈ p3 ∈ R }}).
Proof with solve [eauto].
  simpl.
  induction 1; subst;
    [> split; [intros * HT2; inversion HT2; subst; eauto; clear HT2 | intros * HRT1 HRT2; eauto] ..];
    per_ctx_env_irrel_rewrite.
  - rename tail_rel0 into tail_rel.
    econstructor; eauto.
    + eapply IHper_ctx_env...
    + unfold rel_typ in *.
      intros.
      assert (tail_rel p p) by (etransitivity; [| symmetry]; eassumption).
      destruct_rel_mod_eval.
      per_univ_elem_irrel_rewrite.
      econstructor; eauto.
      eapply per_univ_trans; [| eassumption]...
  - destruct HRT1, HRT2, IHper_ctx_env.
    assert (tail_rel d{{{ p1 ↯ }}} d{{{ p3 ↯ }}}) by mauto.
    eexists.
    unfold rel_typ in *.
    destruct_rel_mod_eval.
    per_univ_elem_irrel_rewrite.
    eapply per_elem_trans...
Qed.
