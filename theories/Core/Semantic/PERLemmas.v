From Coq Require Import Lia PeanoNat Relations.Relation_Definitions RelationClasses Program.Equality.
From Equations Require Import Equations.
From Mcltt Require Import Axioms Base Domain Evaluate EvaluateLemmas LibTactics PER Readback ReadbackLemmas Syntax System.

(* Lemma rel_mod_eval_ex_pull : *)
(*   forall (A : Type) (P : domain -> domain -> relation domain -> A -> Prop) {T p T' p'} R, *)
(*     rel_mod_eval (fun a b R => exists x : A, P a b R x) T p T' p' R <-> *)
(*       exists x : A, rel_mod_eval (fun a b R => P a b R x) T p T' p' R. *)
(* Proof. *)
(*   split; intros. *)
(*   - destruct H. *)
(*     destruct H1 as [? ?]. *)
(*     eexists; econstructor; eauto. *)
(*   - do 2 destruct H; econstructor; eauto. *)
(* Qed. *)

(* Lemma rel_mod_eval_simp_ex : *)
(*   forall (A : Type) (P : domain -> domain -> relation domain -> Prop) (Q : domain -> domain -> relation domain -> A -> Prop) {T p T' p'} R, *)
(*     rel_mod_eval (fun a b R => P a b R /\ exists x : A, Q a b R x) T p T' p' R <-> *)
(*       exists x : A, rel_mod_eval (fun a b R => P a b R /\ Q a b R x) T p T' p' R. *)
(* Proof. *)
(*   split; intros. *)
(*   - destruct H. *)
(*     destruct H1 as [? [? ?]]. *)
(*     eexists; econstructor; eauto. *)
(*   - do 2 destruct H; econstructor; eauto. *)
(*     firstorder. *)
(* Qed. *)

(* Lemma rel_mod_eval_simp_and : *)
(*   forall (P : domain -> domain -> relation domain -> Prop) (Q : relation domain -> Prop) {T p T' p'} R, *)
(*     rel_mod_eval (fun a b R => P a b R /\ Q R) T p T' p' R <-> *)
(*       rel_mod_eval P T p T' p' R /\ Q R. *)
(* Proof. *)
(*   split; intros. *)
(*   - destruct H. *)
(*     destruct H1 as [? ?]. *)
(*     split; try econstructor; eauto. *)
(*   - do 2 destruct H; econstructor; eauto. *)
(* Qed. *)

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
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  specialize (H12 _ _ _ eq_refl H5).
  congruence.
Qed.

Lemma per_univ_elem_right_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i A B' R' ->
    R = R'.
Proof.
  intros. eauto using per_univ_elem_right_irrel_gen.
Qed.

Ltac per_univ_elem_right_irrel_rewrite1 :=
  match goal with
  | H1 : {{ DF ~?A ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }}, H2 : {{ DF ~?A ≈ ~?B' ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
      clean replace R2 with R1 by (eauto using per_univ_elem_right_irrel)
  end.
Ltac per_univ_elem_right_irrel_rewrite := repeat per_univ_elem_right_irrel_rewrite1.

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    per_univ_elem i B A R /\ (forall a b, {{ Dom a ≈ b ∈ R }} <-> {{ Dom b ≈ a ∈ R }}).
Proof.
  intros. induction H using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; trivial.
    + intros. split; intros [].
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
      destruct_rel_mod_eval.
      econstructor; eauto.
      functional_eval_rewrite_clear.
      per_univ_elem_right_irrel_rewrite.
      assumption.

    + assert (forall a b : domain,
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') a c b c') ->
                 (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') b c a c')).
      {
        intros.
        assert (equiv_c'_c : in_rel c' c) by firstorder.
        assert (equiv_c_c : in_rel c c) by (etransitivity; eassumption).
        destruct_rel_mod_eval.
        destruct_rel_mod_app.
        functional_eval_rewrite_clear.
        per_univ_elem_right_irrel_rewrite.
        econstructor; eauto.
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
  intros * []%per_univ_elem_sym []%per_univ_elem_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Lemma per_univ_elem_cross_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i B' A R' ->
    R = R'.
Proof.
  intros * ? []%per_univ_elem_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_rewrite1 :=
  match goal with
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_univ_elem_right_irrel)
    | H1 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?B ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
        clean replace R2 with R1 by (eauto using per_univ_elem_left_irrel)
    | H1 : {{ DF ~?A ≈ ~_ ∈ per_univ_elem ?i ↘ ?R1 }},
        H2 : {{ DF ~_ ≈ ~?A ∈ per_univ_elem ?i ↘ ?R2 }} |- _ =>
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
    forall A3,
    per_univ_elem i A2 A3 R ->
    per_univ_elem i A1 A3 R /\ (forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3).
Proof with solve [mauto].
  induction 1 using per_univ_elem_ind; intros * HT2;
    invert_per_univ_elem HT2; clear HT2.
  - split; mauto.
    intros * [] [].
    per_univ_elem_irrel_rewrite.
    destruct (H1 _ _ _ H0 _ H2) as [? ?].
    econstructor...
  - split; try econstructor...
  - per_univ_elem_irrel_rewrite.
    rename in_rel0 into in_rel.
    specialize (IHper_univ_elem _ equiv_a_a') as [? _].
    split.
    + per_univ_elem_econstructor; mauto.
      intros.
      assert (equiv_c_c : in_rel c c) by (etransitivity; [ | symmetry]; eassumption).
      destruct_rel_mod_eval.
      per_univ_elem_irrel_rewrite.
      firstorder (econstructor; eauto).
    + setoid_rewrite H2.
      intros.
      assert (equiv_c'_c' : in_rel c' c') by (etransitivity; [symmetry | ]; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      per_univ_elem_irrel_rewrite.
      firstorder (econstructor; eauto).
  - split; try per_univ_elem_econstructor...
Qed.
