From Coq Require Import Setoid.
From Mcltt Require Import Base CtxEquiv LibTactics.
From Mcltt Require Export System.
Import Syntax_Notations.

Lemma ctx_eq_refl : forall {Γ}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with solve [mauto].
  induction 1...
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcltt.

Lemma ctx_eq_trans : forall {Γ0 Γ1 Γ2}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with solve [mauto].
  intros * HΓ01 HΓ12.
  gen Γ2.
  induction HΓ01 as [|Γ0 ? T0 i01 T1]; intros; mauto.
  rename HΓ12 into HT1Γ12.
  inversion_clear HT1Γ12 as [|? Γ2' ? i12 T2].
  clear Γ2; rename Γ2' into Γ2.
  set (i := max i01 i12).
  assert {{ Γ0 ⊢ T0 : Type@i }} by mauto using lift_exp_max_left.
  assert {{ Γ2 ⊢ T2 : Type@i }} by mauto using lift_exp_max_right.
  assert {{ Γ0 ⊢ T0 ≈ T1 : Type@i }} by mauto using lift_exp_eq_max_left.
  assert {{ Γ2 ⊢ T1 ≈ T2 : Type@i }} by mauto using lift_exp_eq_max_right.
  econstructor...
Qed.

Add Relation (ctx) (wf_ctx_eq)
    symmetry proved by @ctx_eq_sym
    transitivity proved by @ctx_eq_trans
    as ctx_eq.

Add Parametric Relation (Γ : ctx) (T : typ) : (exp) (fun t t' => {{ Γ ⊢ t ≈ t' : T }})
    symmetry proved by (fun t t' => wf_exp_eq_sym Γ t t' T)
    transitivity proved by (fun t t' t'' => wf_exp_eq_trans Γ t t' T t'')
    as exp_eq.                                                

Add Parametric Relation (Γ Δ : ctx) : (sub) (fun σ τ => {{ Γ ⊢s σ ≈ τ : Δ }})
    symmetry proved by (fun σ τ => wf_sub_eq_sym Γ σ τ Δ)
    transitivity proved by (fun σ τ ρ => wf_sub_eq_trans Γ σ τ Δ ρ)
    as sub_eq.
