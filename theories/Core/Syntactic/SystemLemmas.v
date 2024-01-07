Require Import Unicode.Utf8_core.

Require Import LibTactics.
Require Import Syntactic.Syntax.
Require Import Syntactic.System.

Lemma ctx_decomp : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }} ∧ ∃ i, {{ Γ ⊢ A : Type@i }}.
Proof with solve [mauto].
  intros * HAΓ.
  inversion HAΓ; subst...
Qed.

#[export]
Hint Resolve ctx_decomp : mcltt.

Lemma ctx_decomp_left : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }}.
Proof with solve [eauto].
  intros * HAΓ.
  eapply proj1, ctx_decomp...
Qed.

Lemma ctx_decomp_right : forall {Γ A}, {{ ⊢ Γ , A }} -> ∃ i, {{ Γ ⊢ A : Type@i }}.
Proof with solve [eauto].
  intros * HAΓ.
  eapply proj2, ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcltt.

Lemma lift_exp_ge : forall {Γ A n m}, n <= m -> {{ Γ ⊢ A : Type@n }} -> {{ Γ ⊢ A : Type@m }}.
Proof with solve [mauto].
  intros * Hnm HA.
  induction Hnm...
Qed.

#[export]
Hint Resolve lift_exp_ge : mcltt.

Lemma lift_exp_max_left : forall {Γ A n} m, {{ Γ ⊢ A : Type@n }} -> {{ Γ ⊢ A : Type@(max n m) }}.
Proof with solve [mauto].
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_exp_max_right : forall {Γ A} n {m}, {{ Γ ⊢ A : Type@m }} -> {{ Γ ⊢ A : Type@(max n m) }}.
Proof with solve [mauto].
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma lift_exp_eq_ge : forall {Γ A A' n m}, n <= m -> {{ Γ ⊢ A ≈ A': Type@n }} -> {{ Γ ⊢ A ≈ A' : Type@m }}.
Proof with solve [mauto].
  intros * Hnm HAA'.
  induction Hnm; subst...
Qed.

#[export]
Hint Resolve lift_exp_eq_ge : mcltt.

Lemma lift_exp_eq_max_left : forall {Γ A A' n} m, {{ Γ ⊢ A ≈ A' : Type@n }} -> {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with solve [mauto].
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_exp_eq_max_right : forall {Γ A A'} n {m}, {{ Γ ⊢ A ≈ A' : Type@m }} -> {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with solve [mauto].
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma presup_ctx_eq : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} ∧ {{ ⊢ Δ }}.
Proof with solve [mauto].
  intros * HΓΔ.
  induction HΓΔ as [|* ? []]...
Qed.

Lemma presup_ctx_eq_left : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with solve [eauto].
  intros * HΓΔ.
  eapply proj1, presup_ctx_eq...
Qed.

Lemma presup_ctx_eq_right : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with solve [eauto].
  intros * HΓΔ.
  eapply proj2, presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mcltt.

Lemma exp_eq_refl : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof.
  mauto.
Qed.

Lemma sub_eq_refl : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_refl sub_eq_refl : mcltt.

Lemma presup_sub_ctx : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} ∧ {{ ⊢ Δ }}.
Proof with solve [mauto].
  intros * Hσ.
  induction Hσ; repeat destruct_one_pair...
Qed.

Lemma presup_sub_ctx_left : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof with solve [eauto].
  intros * Hσ.
  eapply proj1, presup_sub_ctx...
Qed.

Lemma presup_sub_ctx_right : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof with solve [eauto].
  intros * Hσ.
  eapply proj2, presup_sub_ctx...
Qed.

#[export]
Hint Resolve presup_sub_ctx presup_sub_ctx_left presup_sub_ctx_right : mcltt.

Lemma presup_exp_ctx : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with solve [mauto].
  intros * HM.
  induction HM...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mcltt.

Lemma presup_sub_eq_ctx : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with solve [mauto].
  intros * Hσσ'.
  induction Hσσ'; repeat destruct_one_pair...
Qed.

Lemma presup_sub_eq_ctx_left : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with solve [eauto].
  intros * Hσσ'.
  eapply proj1, presup_sub_eq_ctx...
Qed.

Lemma presup_sub_eq_ctx_right : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof with solve [eauto].
  intros * Hσσ'.
  eapply proj2, presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mcltt.

Lemma presup_exp_eq_ctx : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof with solve [mauto].
  intros * HMM'.
  induction HMM'...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcltt.

Lemma exp_eq_refl : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_refl : mcltt.

Lemma sub_eq_refl : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve sub_eq_refl : mcltt.

Lemma ctx_eq_sym : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof with solve [mauto].
  intros * HΓΔ.
  induction HΓΔ...
Qed.

#[export]
Hint Resolve ctx_eq_sym : mcltt.

Lemma exp_sub_typ : forall {Δ Γ A σ i}, {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
  mauto.
Qed.

Lemma exp_eq_sub_cong_typ1 : forall {Δ Γ A A' σ i}, {{ Δ ⊢ A ≈ A' : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof.
  mauto.
Qed.

Lemma exp_eq_sub_cong_typ2' : forall {Δ Γ A σ τ i}, {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ τ : Δ }} -> {{ Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof with solve [mauto].
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_compose_typ : forall {Ψ Δ Γ A σ τ i}, {{ Ψ ⊢ A : Type@i }} -> {{ Δ ⊢s σ : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }}.
Proof with solve [mauto].
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_sub_typ exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mcltt.

Lemma exp_eq_typ_sub_sub : forall {Γ Δ Ψ σ τ i}, {{ Δ ⊢s σ : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢ Type@i[σ][τ] ≈ Type@i : Type@(S i) }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mcltt.

Lemma vlookup_0_typ : forall {Γ i}, {{ ⊢ Γ }} -> {{ Γ, Type@i ⊢ # 0 : Type@i }}.
Proof with solve [mauto].
  intros.
  eapply wf_conv...
  Unshelve.
  all: constructor.
Qed.

Lemma vlookup_1_typ : forall {Γ i A j}, {{ ⊢ Γ }} -> {{ Γ, Type@i ⊢ A : Type@j }} -> {{ Γ, Type@i, A ⊢ # 1 : Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ, Type@i }} by mauto.
  assert {{ ⊢ Γ, Type@i, A }} by mauto.
  eapply wf_conv...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcltt.

Lemma exp_eq_var_0_sub_typ : forall {Γ σ Δ M i}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : Type@i }} -> {{ Γ ⊢ #0[σ ,, M] ≈ M : Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ Γ ⊢ M : Type@i[σ] }} by mauto.
  eapply wf_exp_eq_conv...
  Unshelve.
  constructor.
Qed.

Lemma exp_eq_var_1_sub_typ : forall {Γ σ Δ A i M j}, {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A[σ] }} -> {{ #0 : Type@j[Wk] ∈ Δ }} -> {{ Γ ⊢ #1[σ ,, M] ≈ #0[σ] : Type@j }}.
Proof with solve [mauto].
  intros * ? ? ? Hvar0.
  inversion Hvar0 as [? Δ'|]; subst.
  assert {{ ⊢ Δ' }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mcltt.

Lemma exp_eq_var_0_weaken_typ : forall {Γ A i}, {{ ⊢ Γ , A }} -> {{ #0 : Type@i[Wk] ∈ Γ }} -> {{ Γ , A ⊢ #0[Wk] ≈ #1 : Type@i }}.
Proof with solve [mauto].
  intros * ? Hvar0.
  assert {{ ⊢ Γ }} by mauto.
  inversion Hvar0 as [? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by mauto.
  eapply wf_exp_eq_conv; only 1: solve [mauto].
  eapply exp_eq_typ_sub_sub; [|solve [mauto]]...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mcltt.

Lemma sub_extend_typ : forall {Γ σ Δ M i}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : Type@i }} -> {{ Γ ⊢s (σ ,, M) : Δ , Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  econstructor...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve sub_extend_typ : mcltt.

Lemma sub_eq_extend_cong_typ' : forall {Γ σ σ' Δ M M' i}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ Γ ⊢ M ≈ M' : Type@i }} -> {{ Γ ⊢s (σ ,, M) ≈ (σ' ,, M') : Δ , Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  econstructor...
  Unshelve.
  constructor.
Qed.

Lemma sub_eq_extend_compose_typ : forall {Γ τ Γ' σ Γ'' A i M j}, {{ Γ' ⊢s σ : Γ'' }} -> {{ Γ'' ⊢ A : Type@i }} -> {{ Γ' ⊢ M : Type@j }} -> {{ Γ ⊢s τ : Γ' }} -> {{ Γ ⊢s (σ ,, M) ∘ τ ≈ ((σ ∘ τ) ,, M[τ]) : Γ'' , Type@j }}.
Proof with solve [mauto].
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_typ : forall {Γ σ Γ' M i}, {{ Γ' ⊢s σ : Γ }} -> {{ Γ' ⊢ M : Type@i }} -> {{ Γ' ⊢s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ }} by mauto.
  econstructor; only 1,3: solve [mauto]...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ' sub_eq_extend_compose_typ sub_eq_p_extend_typ : mcltt.

Lemma exp_eq_sub_sub_compose_cong_typ : forall {Γ Δ Δ' Ψ σ τ σ' τ' A i}, {{ Ψ ⊢ A : Type@i }} -> {{ Δ ⊢s σ : Ψ }} -> {{ Δ' ⊢s σ' : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢s τ' : Δ' }} -> {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} -> {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }} by mauto.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  assert {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Type@i }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mcltt.

Lemma exp_sub_nat : forall {Δ Γ M σ}, {{ Δ ⊢ M : ℕ }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M[σ] : ℕ }}.
Proof.
  mauto.
  Unshelve.
  constructor.
Qed.

Lemma exp_eq_sub_cong_nat1 : forall {Δ Γ M M' σ}, {{ Δ ⊢ M ≈ M' : ℕ }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof.
  mauto.
  Unshelve.
  constructor.
Qed.

Lemma exp_eq_sub_cong_nat2' : forall {Δ Γ M σ τ}, {{ Δ ⊢ M : ℕ }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ τ : Δ }} -> {{ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with solve [mauto].
  intros.
  eapply wf_exp_eq_conv...
  Unshelve.
  constructor.
Qed.

Lemma exp_eq_sub_compose_nat : forall {Ψ Δ Γ M σ τ}, {{ Ψ ⊢ M : ℕ }} -> {{ Δ ⊢s σ : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with solve [mauto].
  intros.
  eapply wf_exp_eq_conv...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve exp_sub_nat exp_eq_sub_cong_nat1 exp_eq_sub_cong_nat2' exp_eq_sub_compose_nat : mcltt.

Lemma exp_eq_nat_sub_sub : forall {Γ Δ Ψ σ τ i}, {{ Δ ⊢s σ : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Type@i }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub : mcltt.

Lemma exp_eq_nat_sub_sub_to_nat_sub : forall {Γ Δ Ψ Ψ' σ τ σ' i}, {{ Δ ⊢s σ : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢s σ' : Ψ' }} -> {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Type@i }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub_to_nat_sub : mcltt.

Lemma vlookup_0_nat : forall {Γ}, {{ ⊢ Γ }} -> {{ Γ, ℕ ⊢ # 0 : ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ, ℕ ⊢ # 0 : ℕ[Wk] }}...
  Unshelve.
  all: constructor.
Qed.

Lemma vlookup_1_nat : forall {Γ A i}, {{ ⊢ Γ }} -> {{ Γ, ℕ ⊢ A : Type@i }} -> {{ Γ, ℕ, A ⊢ # 1 : ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ, ℕ }} by mauto.
  assert {{ ⊢ Γ, ℕ, A }} by mauto.
  assert {{ Γ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }}...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mcltt.

Lemma exp_eq_var_0_sub_nat : forall {Γ σ Δ M}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : ℕ }} -> {{ Γ ⊢ #0[σ ,, M] ≈ M : ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ Γ ⊢ M : ℕ[σ] }} by mauto.
  assert {{ Γ ⊢ #0[σ,, M] ≈ M : ℕ[σ] }}...
  Unshelve.
  all: constructor.
Qed.

Lemma exp_eq_var_1_sub_nat : forall {Γ σ Δ A i M}, {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A[σ] }} -> {{ #0 : ℕ[Wk] ∈ Δ }} -> {{ Γ ⊢ #1[σ ,, M] ≈ #0[σ] : ℕ }}.
Proof with solve [mauto].
  intros * ? ? ? Hvar0.
  inversion Hvar0 as [? Δ'|]; subst.
  assert {{ ⊢ Δ' }} by mauto.
  assert {{ Γ ⊢ #1[σ,, M] ≈ #0[σ] : ℕ[Wk][σ] }}...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_nat exp_eq_var_1_sub_nat : mcltt.

Lemma exp_eq_var_0_weaken_nat : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ #0 : ℕ[Wk] ∈ Γ }} -> {{ Γ , A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with solve [mauto].
  intros * ? Hvar0.
  assert {{ ⊢ Γ }} by mauto.
  inversion Hvar0 as [? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by mauto.
  assert {{ Γ', ℕ, A ⊢ #0[Wk] ≈ # 1 : ℕ[Wk][Wk] }}...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_nat : mcltt.

Lemma sub_extend_nat : forall {Γ σ Δ M}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : ℕ }} -> {{ Γ ⊢s (σ ,, M) : Δ , ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  econstructor...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve sub_extend_nat : mcltt.

Lemma sub_eq_extend_cong_nat' : forall {Γ σ σ' Δ M M'}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ Γ ⊢ M ≈ M' : ℕ }} -> {{ Γ ⊢s (σ ,, M) ≈ (σ' ,, M') : Δ , ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  econstructor...
  Unshelve.
  all: constructor.
Qed.

Lemma sub_eq_extend_compose_nat : forall {Γ τ Γ' σ Γ'' A i M}, {{ Γ' ⊢s σ : Γ'' }} -> {{ Γ'' ⊢ A : Type@i }} -> {{ Γ' ⊢ M : ℕ }} -> {{ Γ ⊢s τ : Γ' }} -> {{ Γ ⊢s (σ ,, M) ∘ τ ≈ ((σ ∘ τ) ,, M[τ]) : Γ'' , ℕ }}.
Proof with solve [mauto].
  intros.
  econstructor...
  Unshelve.
  all: constructor.
Qed.

Lemma sub_eq_p_extend_nat : forall {Γ σ Γ' M}, {{ Γ' ⊢s σ : Γ }} -> {{ Γ' ⊢ M : ℕ }} -> {{ Γ' ⊢s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ }} by mauto.
  econstructor; only 1,3: solve [mauto]...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_nat' sub_eq_extend_compose_nat sub_eq_p_extend_nat : mcltt.

Lemma exp_eq_sub_sub_compose_cong_nat : forall {Γ Δ Δ' Ψ σ τ σ' τ' M}, {{ Ψ ⊢ M : ℕ }} -> {{ Δ ⊢s σ : Ψ }} -> {{ Δ' ⊢s σ' : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢s τ' : Δ' }} -> {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} -> {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_nat : mcltt.

Lemma exp_eq_sub_sub_compose_cong : forall {Γ Δ Δ' Ψ σ τ σ' τ' M A i}, {{ Ψ ⊢ A : Type@i }} -> {{ Ψ ⊢ M : A }} -> {{ Δ ⊢s σ : Ψ }} -> {{ Δ' ⊢s σ' : Ψ }} -> {{ Γ ⊢s τ : Δ }} -> {{ Γ ⊢s τ' : Δ' }} -> {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} -> {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mcltt.

Lemma ctx_lookup_wf : forall {Γ A x}, {{ ⊢ Γ }} -> {{ #x : A ∈ Γ }} -> ∃ i, {{ Γ ⊢ A : Type@i }}.
Proof with solve [mauto].
  intros * HΓ Hx.
  induction Hx; inversion_clear HΓ; [|assert (exists i, {{ Γ ⊢ A : Type@i }}) as [] by eauto]...
Qed.

#[export]
Hint Resolve ctx_lookup_wf : mcltt.

Lemma ctxeq_ctx_lookup : forall {Γ Δ A x}, {{ ⊢ Γ ≈ Δ }} -> {{ #x : A ∈ Γ }} -> ∃ B i, {{ #x : B ∈ Δ }} ∧ {{ Γ ⊢ A ≈ B : Type@i }} ∧ {{ Δ ⊢ A ≈ B : Type@i }}.
Proof with solve [mauto].
  intros * HΓΔ Hx; gen Δ.
  induction Hx as [|* ? IHHx]; intros; inversion_clear HΓΔ as [|? ? ? ? ? HΓΔ'];
    [|destruct (IHHx _ HΓΔ') as [? [? [? [? ?]]]]]; repeat eexists; repeat split...
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mcltt.

Lemma sub_id_extend : ∀ {Γ M A i}, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with solve [mauto].
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mcltt.

Lemma sub_eq_p_id_extend : ∀ {Γ M A i}, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢s Wk∘(Id ,, M) ≈ Id : Γ }}.
Proof with solve [mauto].
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mcltt.

Lemma sub_q : forall {Γ A i σ Δ}, {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ , A[σ] ⊢s q σ : Δ , A }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ, A[σ] ⊢ # 0 : A[σ][Wk] }} by mauto.
  econstructor; [econstructor| |]...
Qed.

Lemma sub_q_typ : forall {Γ σ Δ i}, {{ Γ ⊢s σ : Δ }} -> {{ Γ , Type@i ⊢s q σ : Δ , Type@i }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ Γ, Type@i ⊢s σ ∘ Wk : Δ }} by (econstructor; mauto).
  assert {{ Γ, Type@i ⊢ # 0 : Type@i[Wk] }} by mauto.
  assert {{ Γ, Type@i ⊢ # 0 : Type@i }}...
Qed.

Lemma sub_q_nat : forall {Γ σ Δ}, {{ Γ ⊢s σ : Δ }} -> {{ Γ , ℕ ⊢s q σ : Δ , ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ Γ, ℕ ⊢s σ ∘ Wk : Δ }} by (econstructor; mauto).
  assert {{ Γ, ℕ ⊢ # 0 : ℕ[Wk] }} by mauto.
  assert {{ Γ, ℕ ⊢ # 0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ sub_q_nat : mcltt.

Lemma exp_eq_var_1_sub_q_sigma_nat : forall {Γ A i σ Δ}, {{ Δ, ℕ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ ⊢ Δ, ℕ }} by mauto.
  assert {{ ⊢ Γ }} by mauto.
  assert {{ ⊢ Γ, ℕ }} by mauto.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by (eapply exp_eq_var_1_sub_nat; mauto).
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto.
  assert {{ Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[Wk] ≈ #1 : ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}...
Qed.

#[export]
Hint Resolve exp_eq_var_1_sub_q_sigma_nat : mcltt.

Lemma sub_id_extend_zero : ∀ {Γ}, {{ ⊢ Γ }} -> {{ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof.
  mauto.
Qed.

Lemma sub_weak_compose_weak_extend_succ_var_1 : ∀ {Γ A i}, {{ Γ, ℕ ⊢ A : Type@i }} -> {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ, ℕ }} by mauto.
  assert {{ ⊢ Γ }} by mauto.
  eapply sub_extend_nat...
Qed.

Lemma sub_eq_id_extend_nat_compose_sigma : ∀ {Γ M σ Δ}, {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ M : ℕ }} -> {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢s (Id ,, M)∘σ ≈ Id∘σ ,, M[σ] : Δ, ℕ }} by (eapply sub_eq_extend_compose_nat; mauto).
  assert {{ Γ ⊢s Id∘σ ,, M[σ] ≈ σ ,, M[σ] : Δ, ℕ }} by (eapply sub_eq_extend_cong_nat'; mauto)...
  Unshelve.
  constructor.
Qed.

Lemma sub_eq_id_extend_compose_sigma : ∀ {Γ M A σ Δ i}, {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Δ ⊢ M : A }} -> {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢s (Id ,, M)∘σ ≈ Id∘σ ,, M[σ] : Δ, A }} by (eapply wf_sub_eq_extend_compose; mauto).
  assert {{ Γ ⊢ M[σ] ≈ M[σ] : A[σ] }} by mauto.
  assert {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_id_extend_zero sub_weak_compose_weak_extend_succ_var_1 sub_eq_id_extend_nat_compose_sigma sub_eq_id_extend_compose_sigma : mcltt.

Lemma sub_eq_sigma_compose_weak_id_extend : ∀ {Γ M A i σ Δ}, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id ,, M)) : Δ }} by mauto.
  assert {{ Γ ⊢s Wk ∘ (Id,, M) ≈ Id : Γ }} by mauto.
  assert {{ Γ ⊢s σ∘(Wk∘(Id ,, M)) ≈ σ∘Id : Δ }}...
Qed.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mcltt.

Lemma sub_eq_q_sigma_id_extend : ∀ {Γ M A i σ Δ}, {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ M : A[σ] }} -> {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof with solve [mauto].
  intros.
  assert {{ Γ ⊢s Id ,, M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  assert {{ Γ ⊢s q σ∘(Id ,, M) ≈ (σ∘Wk)∘(Id ,, M) ,, #0[Id ,, M] : Δ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id ,, M) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto.
  assert {{ Γ ⊢ #0[Id ,, M] ≈ M : A[σ][Id] }} by mauto.
  assert {{ Γ ⊢ #0[Id ,, M] ≈ M : A[σ] }} by mauto.
  assert {{ Γ ⊢ #0[Id ,, M] ≈ M : A[(σ∘Wk)∘(Id ,, M)] }}...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mcltt.

Lemma sub_eq_p_q_sigma : ∀ {Γ A i σ Δ}, {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }}...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mcltt.

Lemma sub_eq_p_q_sigma_nat : ∀ {Γ σ Δ}, {{ Γ ⊢s σ : Δ }} -> {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ }} by mauto.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_nat : mcltt.

Lemma sub_eq_p_p_q_q_sigma_nat : ∀ {Γ A i σ Δ}, {{ Δ, ℕ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Δ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Γ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ ∘ Wk : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk ∘ (q σ ∘ Wk) : Δ }} by mauto.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk ∘ (q σ ∘ Wk) ≈ (Wk ∘ q σ) ∘ Wk : Δ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s (Wk ∘ q σ) ∘ Wk ≈ (σ ∘ Wk) ∘ Wk : Δ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_p_q_q_sigma_nat : mcltt.

Lemma sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : ∀ {Γ A i σ Δ}, {{ Δ, ℕ ⊢ A : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }}.
Proof with solve [mauto].
  intros.
  assert {{ ⊢ Δ }} by mauto.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto.
  set (Γ' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ Wk∘Wk ,, succ #1 }}}).
  assert {{ Γ' ⊢s Wk ∘ Wk : Γ }} by mauto.
  assert {{ Γ' ⊢s WkWksucc : Γ, ℕ }} by mauto.
  assert {{ Γ' ⊢s q σ∘WkWksucc ≈ (σ∘Wk)∘WkWksucc ,, #0[WkWksucc] : Δ, ℕ }} by mauto.
  assert {{ Γ' ⊢ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Δ }} by mauto.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Δ }} by mauto.
  assert {{ Γ' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Δ }} by mauto.
  assert {{ Δ, ℕ, A ⊢s Wk : Δ, ℕ }} by mauto.
  assert {{ Γ' ⊢s q (q σ) : Δ, ℕ, A }} by mauto.
  assert {{ Γ' ⊢s (Wk∘Wk)∘q (q σ) ≈ Wk∘(Wk∘q (q σ)) : Δ }} by mauto.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Δ }} by mauto.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢ succ #1 ≈ succ #1[q (q σ)] : ℕ }} by mauto.
  assert {{ Γ' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc ,, #0[WkWksucc] ≈ (Wk∘Wk)∘q (q σ) ,, (succ #1)[q (q σ)] : Δ, ℕ }} by mauto.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk : Δ }} by mauto.
  assert {{ Δ, ℕ, A ⊢ #1 : ℕ }} by mauto.
  assert {{ Δ, ℕ, A ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢s (Wk∘Wk)∘q (q σ) ,, (succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Δ, ℕ }}...
  Unshelve.
  all: constructor.
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : mcltt.
