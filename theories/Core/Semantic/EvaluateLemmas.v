From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base Domain Evaluate LibTactics Syntax System.

#[local]
Definition functional_eval_exp_prop M p m1 (_ : {{ ⟦ M ⟧ p ↘ m1 }}) : Prop := forall m2 (Heval2: {{ ⟦ M ⟧ p ↘ m2 }}), m1 = m2.
#[local]
Definition functional_eval_natrec_prop A MZ MS m p r1 (_ : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }}) : Prop := forall r2 (Heval2 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r2 }}), r1 = r2.
#[local]
Definition functional_eval_app_prop m n r1 (_ : {{ $| m & n |↘ r1 }}) : Prop := forall r2 (Heval2 : {{ $| m & n |↘ r2 }}), r1 = r2.
#[local]
Definition functional_eval_sub_prop σ p p1 (_ : {{ ⟦ σ ⟧s p ↘ p1 }}) : Prop := forall p2 (Heval2 : {{ ⟦ σ ⟧s p ↘ p2 }}), p1 = p2.
Arguments functional_eval_exp_prop /.
Arguments functional_eval_natrec_prop /.
Arguments functional_eval_app_prop /.
Arguments functional_eval_sub_prop /.

Lemma functional_eval_exp : forall {M p m1}, {{ ⟦ M ⟧ p ↘ m1 }} -> forall m2 (Heval2: {{ ⟦ M ⟧ p ↘ m2 }}), m1 = m2
with functional_eval_natrec : forall {A MZ MS m p r1}, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }} -> forall r2 (Heval2 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r2 }}), r1 = r2
with functional_eval_app : forall {m n r1}, {{ $| m & n |↘ r1 }} -> forall r2 (Heval2 : {{ $| m & n |↘ r2 }}), r1 = r2
with functional_eval_sub : forall {σ p p1}, {{ ⟦ σ ⟧s p ↘ p1 }} -> forall p2 (Heval2 : {{ ⟦ σ ⟧s p ↘ p2 }}), p1 = p2.
Proof with mauto.
  all: clear functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub; intros * Heval1.
  - (* functional_eval_exp *)
    induction Heval1
      using eval_exp_mut_ind
      with (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      simpl in *; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      solve [mauto|erewrite IHHeval1 in *; mauto|erewrite IHHeval1_1, IHHeval1_2 in *; mauto].
  - (* functional_eval_natrec *)
    induction Heval1
      using eval_natrec_mut_ind
      with (P := functional_eval_exp_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      simpl in *; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      solve [mauto|erewrite IHHeval1 in *; mauto|erewrite IHHeval1, IHHeval0 in *; mauto].
  - (* functional_eval_app *)
    induction Heval1
      using eval_app_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P2 := functional_eval_sub_prop);
      simpl in *; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      solve [mauto|erewrite IHHeval1 in *; mauto|erewrite IHHeval1, IHHeval0 in *; mauto].
  - (* functional_eval_sub *)
    induction Heval1
      using eval_sub_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop);
      simpl in *; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      try solve [mauto|erewrite IHHeval1 in *; mauto|erewrite IHHeval1, IHHeval0 in *; mauto|erewrite IHHeval1_1 in *; mauto].
Qed.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub : mcltt.
