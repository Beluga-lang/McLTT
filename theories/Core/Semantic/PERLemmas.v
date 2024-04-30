From Coq Require Import Lia PeanoNat Relations ChoiceFacts Program.Equality.
From Equations Require Import Equations.
From Mcltt Require Import Axioms Base Domain Evaluate EvaluateLemmas LibTactics PER Readback ReadbackLemmas Syntax System.

Lemma per_bot_sym : forall m n,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with mauto.
  intros * H s.
  destruct (H s) as [? []]...
Qed.

#[export]
Hint Resolve per_bot_sym : mcltt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof.
  intros * Hmn Hnl s.
  destruct (Hmn s) as [L []].
  destruct (Hnl s) as [L' []].
  replace L' with L in *; mauto.
Qed.

#[export]
Hint Resolve per_bot_trans : mcltt.

Lemma per_nat_sym : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof.
  intros *.
  induction 1; econstructor; mauto.
Qed.

#[export]
Hint Resolve per_nat_sym : mcltt.

Lemma per_nat_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof.
  intros * H. gen l.
  induction H; intros * H'; inversion_clear H'; econstructor; mauto.
Qed.

#[export]
Hint Resolve per_nat_trans : mcltt.

Lemma per_ne_sym : forall m n,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof.
  intros * [].
  econstructor.
  mauto.
Qed.

#[export]
Hint Resolve per_ne_sym : mcltt.

Lemma per_ne_trans : forall m n l,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with mauto.
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
  simp per_univ_elem in Hright; inversion Hright; try congruence; subst.
  rewrite <- per_univ_elem_equation_1 in *.
  specialize (IHper_univ_elem _ _ _ eq_refl equiv_a_a').
  subst.
  extensionality f.
  extensionality f'.
  rewrite H1, H8.
  extensionality c.
  extensionality c'.
  extensionality equiv_c_c'.
  specialize (H0 _ _ equiv_c_c') as [a ? ? ? [? ?]].
  specialize (H7 _ _ equiv_c_c') as [a0 ? ? ? ?].
  replace a0 with a in * by mauto.
  specialize (H4 _ _ _ eq_refl H7).
  congruence.
Qed.

Lemma per_univ_elem_right_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i A B' R' ->
    R = R'.
Proof.
  intros. eauto using per_univ_elem_right_irrel_gen.
Qed.

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    exists R', per_univ_elem i B A R' /\ (forall a b, {{ Dom a ≈ b ∈ R }} <-> {{ Dom b ≈ a ∈ R' }}).
Proof.
  intros. induction H using per_univ_elem_ind; subst.
  - exists (per_univ j'). split.
    + apply per_univ_elem_core_univ'; trivial.
    + intros. split; intros HD; destruct HD.
      * specialize (H1 _ _ _ H0).
        firstorder.
      * specialize (H1 _ _ _ H0).
        firstorder.
  - exists per_nat. split.
    + econstructor.
    + intros; split; mauto.
  - destruct IHper_univ_elem as [in_rel' [? ?]].
    setoid_rewrite rel_mod_eval_simp_ex in H0.
    repeat setoid_rewrite dep_functional_choice_equiv in H0.
    destruct H0 as [out_rel' ?].
    assert (forall a b : domain, in_rel' a b -> in_rel b a) as Hconv by firstorder.
    assert (forall a b : domain, in_rel a b -> in_rel' b a) as Hconv' by firstorder.
    setoid_rewrite H1.
    exists (fun f f' => forall (c c' : domain) (equiv_c_c' : in_rel' c c'), rel_mod_app (out_rel' c' c (Hconv _ _ equiv_c_c')) f c f' c').
    split.
    + simp per_univ_elem; econstructor; try rewrite <- per_univ_elem_equation_1 in *; eauto.
      * intros.
        destruct (H0 _ _ (Hconv _ _ equiv_c_c')) as [? ? ? ? [? [? ?]]].
        econstructor; eauto.
        apply H7.
      * auto.
    + split; intros.
      * destruct (H0 _ _ (Hconv _ _ equiv_c_c')) as [? ? ? ? [? [? ?]]].
        specialize (H4 _ _ (Hconv c c' equiv_c_c')).
        destruct H4; econstructor; eauto; firstorder.
      * destruct (H0 _ _ equiv_c_c') as [? ? ? ? [? [? ?]]].
        specialize (H4 _ _ (Hconv' _ _ equiv_c_c')).
        destruct H4; econstructor; eauto; firstorder.
        replace (Hconv c' c (Hconv' c c' equiv_c_c')) with equiv_c_c' in H11 by apply proof_irrelevance.
        firstorder.
  - exists per_ne. split.
    + econstructor.
    + intros; split; mauto.
Qed.

(* Ltac invert_per_univ_elem H := *)
(*   simp per_univ_elem in H; *)
(*   inversion H; *)
(*   subst; *)
(*   try rewrite <- per_univ_elem_equation_1 in *. *)

(* Ltac per_univ_elem_econstructor := *)
(*   simp per_univ_elem; *)
(*   econstructor; *)
(*   try rewrite <- per_univ_elem_equation_1 in *. *)

(* Lemma per_univ_elem_trans : forall i A1 A2 R1, *)
(*     per_univ_elem i A1 A2 R1 -> *)
(*     forall A3 R2, *)
(*     per_univ_elem i A2 A3 R2 -> *)
(*     exists R3, per_univ_elem i A1 A3 R3 /\ (forall a1 a2 a3, R1 a1 a2 -> R2 a2 a3 -> R3 a1 a3). *)
(* Proof. *)
(*   induction 1 using per_univ_elem_ind; intros ? ? HT2; *)
(*     invert_per_univ_elem HT2. *)
(*   - exists (per_univ j'0). *)
(*     split. *)
(*     + apply per_univ_elem_core_univ'; trivial. *)
(*     + intros. unfold per_univ in *. *)
(*       destruct H0, H2. *)
(*       destruct (H1 _ _ _ H0 _ _ H2) as [? [? ?]]. *)
(*       eauto. *)
(*   - exists per_nat. *)
(*     split... *)
(*     + mauto. *)
(*     + eapply per_nat_trans. *)
(*   - specialize (IHper_univ_elem _ _ equiv_a_a'). *)
(*     destruct IHper_univ_elem as [in_rel3 [? ?]]. *)
