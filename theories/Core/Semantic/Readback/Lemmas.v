From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base Evaluation LibTactics Readback.Definitions.
Import Domain_Notations.

Section functional_read.
  Let functional_read_nf_prop s m M1 (_ : {{ Rnf m in s ↘ M1 }}) : Prop := forall M2 (Hread2: {{ Rnf m in s ↘ M2 }}), M1 = M2.
  Let functional_read_ne_prop s m M1 (_ : {{ Rne m in s ↘ M1 }}) : Prop := forall M2 (Hread2 : {{ Rne m in s ↘ M2 }}), M1 = M2.
  Let functional_read_typ_prop s m M1 (_ : {{ Rtyp m in s ↘ M1 }}) : Prop := forall M2 (Hread2 : {{ Rtyp m in s ↘ M2 }}), M1 = M2.

  #[local]
  Ltac unfold_functional_read := unfold functional_read_nf_prop, functional_read_ne_prop, functional_read_typ_prop in *.

  Lemma functional_read_nf : forall s m M1 (Hread1: {{ Rnf m in s ↘ M1 }}), functional_read_nf_prop s m M1 Hread1.
  Proof using Type with mauto .
    intros *.
    induction Hread1
      using read_nf_mut_ind
      with (P0 := functional_read_ne_prop)
           (P1 := functional_read_typ_prop);
      unfold_functional_read; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      functional_eval_rewrite_clear; f_equal...
  Qed.

  Lemma functional_read_ne : forall s m M1 (Hread1 : {{ Rne m in s ↘ M1 }}), functional_read_ne_prop s m M1 Hread1.
  Proof using Type with mauto.
    intros *.
    induction Hread1
      using read_ne_mut_ind
      with (P := functional_read_nf_prop)
           (P1 := functional_read_typ_prop);
      unfold_functional_read; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      functional_eval_rewrite_clear; f_equal...
  Qed.

  Lemma functional_read_typ : forall s m M1 (Hread1 : {{ Rtyp m in s ↘ M1 }}), functional_read_typ_prop s m M1 Hread1.
  Proof using Type with mauto.
    intros *.
    induction Hread1
      using read_typ_mut_ind
      with (P := functional_read_nf_prop)
           (P0 := functional_read_ne_prop);
      unfold_functional_read; mauto;
      intros; inversion Hread2; clear Hread2; subst;
      functional_eval_rewrite_clear; f_equal...
  Qed.
End functional_read.

#[export]
Hint Resolve functional_read_nf functional_read_ne functional_read_typ : mcltt.

Ltac functional_read_rewrite_clear1 :=
  match goal with
  | H1 : {{ Rnf ~?m in ?s ↘ ~?M1 }}, H2 : {{ Rnf ~?m in ?s ↘ ~?M2 }} |- _ =>
      clean replace M2 with M1 by mauto; clear H2
  | H1 : {{ Rne ~?m in ?s ↘ ~?M1 }}, H2 : {{ Rne ~?m in ?s ↘ ~?M2 }} |- _ =>
      clean replace M2 with M1 by mauto; clear H2
  | H1 : {{ Rtyp ~?m in ?s ↘ ~?M1 }}, H2 : {{ Rtyp ~?m in ?s ↘ ~?M2 }} |- _ =>
      clean replace M2 with M1 by mauto; clear H2
  end.
Ltac functional_read_rewrite_clear := repeat functional_read_rewrite_clear1.
