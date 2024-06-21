From Mcltt Require Import Base LibTactics CtxSub.
From Mcltt Require Export System.
Import Syntax_Notations.

Lemma ctx_eq_refl : forall {Γ}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcltt.

Lemma ctx_eq_sym : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_eq_sym : mcltt.

Lemma ctx_eq_subtyping : forall Γ Δ,
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_subtyping : mcltt.

Lemma ctxeq_exp : forall {Γ Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof. mauto. Qed.

Lemma ctxeq_exp_eq : forall {Γ Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof. mauto. Qed.

Lemma ctxeq_sub : forall {Γ Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof. mauto. Qed.

Lemma ctxeq_sub_eq : forall {Γ Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof. mauto. Qed.

Lemma ctxeq_subtyping : forall {Γ Δ A B}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ⊆ B }} -> {{ Δ ⊢ A ⊆ B }}.
Proof. mauto. Qed.

#[export]
  Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq ctxeq_subtyping : mcltt.


Lemma ctx_eq_trans : forall {Γ0 Γ1 Γ2}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01 as [|Γ0 ? T0 i01 T1]; mauto.
  inversion_clear 1 as [|? Γ2' ? i12 T2].
  clear Γ2; rename Γ2' into Γ2.
  set (i := max i01 i12).
  assert {{ Γ0 ⊢ T0 : Type@i }} by mauto using lift_exp_max_left.
  assert {{ Γ2 ⊢ T2 : Type@i }} by mauto using lift_exp_max_right.
  assert {{ Γ0 ⊢ T0 ≈ T1 : Type@i }} by mauto using lift_exp_eq_max_left.
  assert {{ Γ2 ⊢ T1 ≈ T2 : Type@i }} by mauto using lift_exp_eq_max_right.
  assert {{ ⊢ Γ0 ≈ Γ2 }} by mauto.
  assert {{ Γ0 ⊢ T0 ≈ T2 : Type@i }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve ctx_eq_trans : mcltt.

#[export]
Instance wf_ctx_PER : PER wf_ctx_eq.
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.
