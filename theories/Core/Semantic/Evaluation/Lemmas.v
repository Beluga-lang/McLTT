From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base LibTactics Evaluation.Definitions.
Import Domain_Notations.

Section functional_eval.
  Let functional_eval_exp_prop M p m1 (_ : {{ ⟦ M ⟧ p ↘ m1 }}) : Prop := forall m2 (Heval2: {{ ⟦ M ⟧ p ↘ m2 }}), m1 = m2.
  Let functional_eval_natrec_prop A MZ MS m p r1 (_ : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }}) : Prop := forall r2 (Heval2 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r2 }}), r1 = r2.
  Let functional_eval_app_prop m n r1 (_ : {{ $| m & n |↘ r1 }}) : Prop := forall r2 (Heval2 : {{ $| m & n |↘ r2 }}), r1 = r2.
  Let functional_eval_sub_prop σ p p1 (_ : {{ ⟦ σ ⟧s p ↘ p1 }}) : Prop := forall p2 (Heval2 : {{ ⟦ σ ⟧s p ↘ p2 }}), p1 = p2.

  #[local]
  Ltac unfold_functional_eval :=
    unfold functional_eval_exp_prop, functional_eval_natrec_prop, functional_eval_app_prop, functional_eval_sub_prop in *;
    clear functional_eval_exp_prop functional_eval_natrec_prop functional_eval_app_prop functional_eval_sub_prop.

  Lemma functional_eval_exp : forall M p m1 (Heval1 : {{ ⟦ M ⟧ p ↘ m1 }}), functional_eval_exp_prop M p m1 Heval1.
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    induction Heval1
      using eval_exp_mut_ind
      with (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval;
      inversion_clear 1; do 2 f_equal...
  Qed.

  Lemma functional_eval_natrec : forall A MZ MS m p r1 (Heval1 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }}), functional_eval_natrec_prop A MZ MS m p r1 Heval1.
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    induction Heval1
      using eval_natrec_mut_ind
      with (P := functional_eval_exp_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval;
      inversion_clear 1; do 2 f_equal...
  Qed.

  Lemma functional_eval_app : forall m n r1 (Heval1 : {{ $| m & n |↘ r1 }}), functional_eval_app_prop m n r1 Heval1.
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    induction Heval1
      using eval_app_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval;
      inversion_clear 1; do 2 f_equal...
  Qed.

  Lemma functional_eval_sub : forall σ p p1 (Heval1 : {{ ⟦ σ ⟧s p ↘ p1 }}), functional_eval_sub_prop σ p p1 Heval1.
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    induction Heval1
      using eval_sub_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop);
      unfold_functional_eval;
      inversion_clear 1; do 2 f_equal...
  Qed.
End functional_eval.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub : mcltt.

Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ⟦ ~?M ⟧ ~?p ↘ ~?m1 }}, H2 : {{ ⟦ ~?M ⟧ ~?p ↘ ~?m2 }} |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : {{ $| ~?m & ~?n |↘ ~?r1 }}, H2 : {{ $| ~?m & ~?n |↘ ~?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ rec ~?m ⟦return ~?A | zero -> ~?MZ | succ -> ~?MS end⟧ ~?p ↘ ~?r1 }}, H2 : {{ rec ~?m ⟦return ~?A | zero -> ~?MZ | succ -> ~?MS end⟧ ~?p ↘ ~?r2 }} |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : {{ ⟦ ~?σ ⟧s ~?p ↘ ~?p1 }}, H2 : {{ ⟦ ~?σ ⟧s ~?p ↘ ~?p2 }} |- _ =>
      clean replace p2 with p1 by first [solve [mauto 2] | tactic_error p2 p1]; clear H2
  end.
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.
