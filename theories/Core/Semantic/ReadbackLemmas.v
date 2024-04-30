From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base Domain Evaluate EvaluateLemmas LibTactics Readback Syntax System.

Definition functional_read_nf_prop s m M1 (_ : {{ Rnf m in s ↘ M1 }}) : Prop := forall M2 (Hread2: {{ Rnf m in s ↘ M2 }}), M1 = M2.
Definition functional_read_ne_prop s m M1 (_ : {{ Rne m in s ↘ M1 }}) : Prop := forall M2 (Hread2 : {{ Rne m in s ↘ M2 }}), M1 = M2.
Definition functional_read_typ_prop s m M1 (_ : {{ Rtyp m in s ↘ M1 }}) : Prop := forall M2 (Hread2 : {{ Rtyp m in s ↘ M2 }}), M1 = M2.

Ltac unfold_functional_read_prop := unfold functional_read_nf_prop, functional_read_ne_prop, functional_read_typ_prop in *.

Lemma functional_read_nf : forall {s m M1} (Hread1 : {{ Rnf m in s ↘ M1 }}), functional_read_nf_prop s m M1 Hread1
with functional_read_ne : forall {s m M1} (Hread1 : {{ Rne m in s ↘ M1 }}), functional_read_ne_prop s m M1 Hread1
with functional_read_typ : forall {s m M1} (Hread1 : {{ Rtyp m in s ↘ M1 }}), functional_read_typ_prop s m M1 Hread1.
Proof with mauto.
  all: clear functional_read_nf functional_read_ne functional_read_typ; intros.
  - (* functional_read_nf *)
    induction Hread1
      using read_nf_mut_ind
      with (P0 := functional_read_ne_prop)
           (P1 := functional_read_typ_prop);
      unfold_functional_read_prop; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      try replace m'0 with m' in * by (eapply functional_eval_app; mauto);
      try replace b0 with b in * by (eapply functional_eval_exp; mauto);
      try replace bz0 with bz in * by (eapply functional_eval_exp; mauto);
      try replace bs0 with bs in * by (eapply functional_eval_exp; mauto);
      try replace ms0 with ms in * by (eapply functional_eval_exp; mauto);
      f_equal...
  - (* functional_read_ne *)
    induction Hread1
      using read_ne_mut_ind
      with (P := functional_read_nf_prop)
           (P1 := functional_read_typ_prop);
      unfold_functional_read_prop; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      try replace m'0 with m' in * by (eapply functional_eval_app; mauto);
      try replace b0 with b in * by (eapply functional_eval_exp; mauto);
      try replace bz0 with bz in * by (eapply functional_eval_exp; mauto);
      try replace bs0 with bs in * by (eapply functional_eval_exp; mauto);
      try replace ms0 with ms in * by (eapply functional_eval_exp; mauto);
      f_equal...
  - (* functional_read_typ *)
    induction Hread1
      using read_typ_mut_ind
      with (P := functional_read_nf_prop)
           (P0 := functional_read_ne_prop);
      unfold_functional_read_prop; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      try replace m'0 with m' in * by (eapply functional_eval_app; mauto);
      try replace b0 with b in * by (eapply functional_eval_exp; mauto);
      try replace bz0 with bz in * by (eapply functional_eval_exp; mauto);
      try replace bs0 with bs in * by (eapply functional_eval_exp; mauto);
      try replace ms0 with ms in * by (eapply functional_eval_exp; mauto);
      f_equal...
Qed.

#[global]
Hint Resolve functional_read_nf functional_read_ne functional_read_typ : mcltt.
