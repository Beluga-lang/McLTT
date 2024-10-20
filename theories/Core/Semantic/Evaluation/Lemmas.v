From Coq Require Import Lia PeanoNat Relations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

Section functional_eval.
  Lemma functional_eval :
    (forall M ρ m1,
        {{ ⟦ M ⟧ ρ ↘ m1 }} ->
        forall m2,
          {{ ⟦ M ⟧ ρ ↘ m2 }} ->
          m1 = m2) /\
      (forall A MZ MS m ρ r1,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r1 }} ->
          forall r2,
            {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r2 }} ->
            r1 = r2) /\
      (forall m n r1,
          {{ $| m & n |↘ r1 }} ->
          forall r2,
            {{ $| m & n |↘ r2 }} ->
            r1 = r2) /\
      (forall a B BR m1 m2 n ρ r1,
          {{ eqrec n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ r1 }} ->
          forall r2,
            {{ eqrec n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ r2 }} ->
            r1 = r2) /\
      (forall σ ρ ρσ1,
          {{ ⟦ σ ⟧s ρ ↘ ρσ1 }} ->
          forall ρσ2,
            {{ ⟦ σ ⟧s ρ ↘ ρσ2 }} ->
            ρσ1 = ρσ2).
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    apply eval_mut_ind; intros;
      progressive_inversion; do 2 f_equal; try reflexivity...
  Qed.

  Corollary functional_eval_exp : forall M ρ m1 m2,
      {{ ⟦ M ⟧ ρ ↘ m1 }} ->
      {{ ⟦ M ⟧ ρ ↘ m2 }} ->
      m1 = m2.
  Proof.
    pose proof functional_eval; firstorder.
  Qed.

  Corollary functional_eval_natrec : forall A MZ MS m ρ r1 r2,
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r1 }} ->
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r2 }} ->
      r1 = r2.
  Proof.
    pose proof functional_eval; intuition.
  Qed.

  Corollary functional_eval_app : forall m n r1 r2,
      {{ $| m & n |↘ r1 }} ->
      {{ $| m & n |↘ r2 }} ->
      r1 = r2.
  Proof.
    pose proof functional_eval; intuition.
  Qed.

  Corollary functional_eval_eqrec : forall a B BR m1 m2 n ρ r1 r2,
      {{ eqrec n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ r1 }} ->
      {{ eqrec n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ r2 }} ->
      r1 = r2.
  Proof.
    pose proof functional_eval; intuition.
  Qed.

  Corollary functional_eval_sub : forall σ ρ ρσ1 ρσ2,
      {{ ⟦ σ ⟧s ρ ↘ ρσ1 }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ2 }} ->
      ρσ1 = ρσ2.
  Proof.
    pose proof functional_eval; firstorder.
  Qed.
End functional_eval.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_eqrec functional_eval_sub : mcltt.

Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m1 }},
      H2 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m2 }} |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : {{ $| ^?m & ^?n |↘ ^?r1 }},
      H2 : {{ $| ^?m & ^?n |↘ ^?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?r1 }},
      H2 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ eqrec ^?n as Eq ^?a ^?m1 ^?m2 ⟦return ^?B | refl -> ^?BR end⟧ ^?ρ ↘ ^?r1 }},
      H2 : {{ eqrec ^?n as Eq ^?a ^?m1 ^?m2 ⟦return ^?B | refl -> ^?BR end⟧ ^?ρ ↘ ^?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ ⟦ ^?σ ⟧s ^?ρ ↘ ^?ρσ1 }},
      H2 : {{ ⟦ ^?σ ⟧s ^?ρ ↘ ^?ρσ2 }} |- _ =>
      clean replace ρσ2 with ρσ1 by first [solve [mauto 2] | tactic_error ρσ2 ρσ1]; clear H2
  end.
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.
