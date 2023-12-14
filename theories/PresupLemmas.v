Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.
Require Import Mcltt.CtxEquiv.
Require Import Setoid.

(*Type lifting lemmas*)

Lemma lift_tm_ge : forall {Γ T n m}, n <= m -> Γ ⊢ T : typ n -> Γ ⊢ T : typ m.
Proof with mauto.
  intros * Hnm HT.
  induction m; inversion Hnm; subst...
Qed.

#[export]
Hint Resolve lift_tm_ge : mcltt.

Lemma lift_tm_max_left : forall {Γ T n} m, Γ ⊢ T : typ n -> Γ ⊢ T : typ (max n m).
Proof with mauto.
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_tm_max_right : forall {Γ T} n {m}, Γ ⊢ T : typ m -> Γ ⊢ T : typ (max n m).
Proof with mauto.
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma lift_eq_ge : forall {Γ T T' n m}, n <= m -> Γ ⊢ T ≈ T': typ n -> Γ ⊢ T ≈ T' : typ m.
Proof with mauto.
  intros * Hnm HTT'.
  induction m; inversion Hnm; subst...
Qed.

#[export]
Hint Resolve lift_eq_ge : mcltt.

Lemma lift_eq_max_left : forall {Γ T T' n} m, Γ ⊢ T ≈ T' : typ n -> Γ ⊢ T ≈ T' : typ (max n m).
Proof with mauto.
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_eq_max_right : forall {Γ T T'} n {m}, Γ ⊢ T ≈ T' : typ m -> Γ ⊢ T ≈ T' : typ (max n m).
Proof with mauto.
  intros.
  assert (m <= max n m) by lia...
Qed.
