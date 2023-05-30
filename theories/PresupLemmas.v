Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.
Require Import Mcltt.CtxEquiv.
Require Import Setoid.

(*Type lifting lemmas*)



Lemma lift_tm_ge (Γ : Ctx) (T : Typ) (n m : nat) : n <= m -> Γ ⊢ T : typ n -> Γ ⊢ T : typ m.
Proof.
  intros.
  induction m.
  assert (n = 0) by lia.
  rewrite H1 in H0.
  exact H0.

  inversion H.
  rewrite <- H1.
  exact H0.
  pose proof (IHm H2).
  mauto.
Qed.  
  

Lemma lift_tm_max (Γ Δ : Ctx) (T T' : Typ) (n m : nat) : Γ ⊢ T : typ n -> Δ ⊢ T' : typ m -> Γ ⊢ T : typ (max n m) ∧ Δ ⊢ T' : typ (max n m).
Proof.
  intros.
  assert (n <= max n m) by lia.
  assert (m <= max n m) by lia.
  split;eauto using lift_tm_ge.
Qed.

Lemma lift_eq_ge (Γ : Ctx) (T T': Typ) (n m : nat) : n <= m -> Γ ⊢ T ≈ T': typ n -> Γ ⊢ T ≈ T' : typ m.
Proof.
  intros.
  induction m.
  assert (n = 0) by lia.
  rewrite H1 in H0.
  exact H0.

  inversion H.
  rewrite <- H1.
  exact H0.
  pose proof (IHm H2).
  mauto.
Qed.  

Lemma lift_eq_max (Γ Δ : Ctx) (T0 T0' T1 T1' : Typ) (n m : nat) : Γ ⊢ T0 ≈ T0' : typ n -> Δ ⊢ T1 ≈ T1' : typ m -> Γ ⊢ T0 ≈ T0' : typ (max n m) ∧ Δ ⊢ T1 ≈ T1' : typ (max n m).
Proof.
  intros.
  assert (n <= max n m) by lia.
  assert (m <= max n m) by lia.
  split;eauto using lift_eq_ge.
Qed.
