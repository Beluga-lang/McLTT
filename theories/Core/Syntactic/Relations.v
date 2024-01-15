Require Import Unicode.Utf8_core.
Require Import Setoid.
Require Import Coq.Program.Equality.

Require Import LibTactics.
Require Import Syntactic.Syntax.
Require Import Syntactic.System.
Require Import Syntactic.SystemLemmas.
Require Import Syntactic.CtxEquiv.

Lemma ctx_eq_refl : forall {Γ}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mauto.
  intros * HΓ.
  induction HΓ...
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcltt.

Lemma ctx_eq_trans : forall {Γ0 Γ1 Γ2}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mauto.
  intros * HΓ01 HΓ12.
  gen Γ2.
  induction HΓ01 as [|? ? ? i01 * HΓ01 IHΓ01 HΓ0T0 _ HΓ0T01 _]; intros...
  rename HΓ12 into HT1Γ12.
  inversion_clear HT1Γ12 as [|? ? ? i12 * HΓ12' _ HΓ2'T2 _ HΓ2'T12].
  pose proof (lift_exp_max_left i12 HΓ0T0).
  pose proof (lift_exp_max_right i01 HΓ2'T2).
  pose proof (lift_exp_eq_max_left i12 HΓ0T01).
  pose proof (lift_exp_eq_max_right i01 HΓ2'T12).
  econstructor...
Qed.

Add Relation (ctx) (wf_ctx_eq)
    symmetry proved by @ctx_eq_sym
    transitivity proved by @ctx_eq_trans
    as ctx_eq.

Add Parametric Relation (Γ : ctx) (T : typ) : (exp) (λ t t', {{ Γ ⊢ t ≈ t' : T }})
    symmetry proved by (λ t t', wf_exp_eq_sym Γ t t' T)
    transitivity proved by (λ t t' t'', wf_exp_eq_trans Γ t t' T t'')
    as exp_eq.                                                

Add Parametric Relation (Γ Δ : ctx) : (sub) (λ σ τ, {{ Γ ⊢s σ ≈ τ : Δ }})
    symmetry proved by (λ σ τ, wf_sub_eq_sym Γ σ τ Δ)
    transitivity proved by (λ σ τ ρ, wf_sub_eq_trans Γ σ τ Δ ρ)
    as sub_eq.
