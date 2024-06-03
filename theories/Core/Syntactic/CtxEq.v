From Mcltt Require Import Base LibTactics.
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

Module ctxeq_judg.
  #[local]
  Ltac gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper H :=
  match type of H with
  | {{ ~?Γ ⊢ ~?M : ~?A }} => pose proof ctxeq_exp_helper _ _ _ H
  | {{ ~?Γ ⊢ ~?M ≈ ~?N : ~?A }} => pose proof ctxeq_exp_eq_helper _ _ _ _ H
  | {{ ~?Γ ⊢s ~?σ : ~?Δ }} => pose proof ctxeq_sub_helper _ _ _ H
  | {{ ~?Γ ⊢s ~?σ ≈ ~?τ : ~?Δ }} => pose proof ctxeq_sub_eq_helper _ _ _ _ H
  end.

  #[local]
  Lemma ctxeq_exp_helper : forall {Γ M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M : A }}
  with
  ctxeq_exp_eq_helper : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M ≈ M' : A }}
  with
  ctxeq_sub_helper : forall {Γ Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ : Γ' }}
  with
  ctxeq_sub_eq_helper : forall {Γ Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper);
      clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
      intros * HΓΔ; destruct (presup_ctx_eq HΓΔ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    (* ctxeq_exp_helper & ctxeq_exp_eq_helper recursion cases *)
    1,6-8: assert {{ ⊢ Γ, ℕ ≈ Δ, ℕ }} by (econstructor; mautosolve);
      assert {{ Δ, ℕ ⊢ B : Type@i }} by eauto; econstructor...
    (* ctxeq_exp_helper & ctxeq_exp_eq_helper function cases *)
    1-3,5-9: assert {{ Δ ⊢ B : Type@i }} by eauto; assert {{ ⊢ Γ, B ≈ Δ, B }} by mauto;
      try econstructor...
    (* ctxeq_exp_helper & ctxeq_exp_eq_helper variable cases *)
    1-2: assert (exists B i, {{ #x : B ∈ Δ }} /\ {{ Γ ⊢ A ≈ B : Type@i }} /\ {{ Δ ⊢ A ≈ B : Type@i }}); destruct_conjs; mautosolve 4.
    (* ctxeq_sub_helper & ctxeq_sub_eq_helper weakening cases *)
    2-3: inversion_clear HΓΔ; econstructor; mautosolve 4.

    (* ctxeq_exp_eq_helper variable case *)
    inversion_clear HΓΔ as [|? Δ0 ? ? C'].
    assert (exists D i', {{ #x : D ∈ Δ0 }} /\ {{ Γ0 ⊢ B ≈ D : Type@i' }} /\ {{ Δ0 ⊢ B ≈ D : Type@i' }}) as [D [i0 ?]] by mauto.
    destruct_conjs.
    assert {{ ⊢ Δ0, C' }} by mauto.
    assert {{ Δ0 ⊢ D ≈ B : Type@i0 }} by mauto.
    assert {{ Δ0, C' ⊢ D[Wk] ≈ B[Wk] : Type@i0 }}...
  Qed.

  Corollary ctxeq_exp : forall {Γ Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
  Proof.
    eauto using ctxeq_exp_helper.
  Qed.

  Corollary ctxeq_exp_eq : forall {Γ Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
  Proof.
    eauto using ctxeq_exp_eq_helper.
  Qed.

  Corollary ctxeq_sub : forall {Γ Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
  Proof.
    eauto using ctxeq_sub_helper.
  Qed.

  Corollary ctxeq_sub_eq : forall {Γ Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
  Proof.
    eauto using ctxeq_sub_eq_helper.
  Qed.

  #[export]
  Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq : mcltt.
End ctxeq_judg.

Export ctxeq_judg.

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
