Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.
Require Import Mcltt.CtxEquiv.
Require Import Mcltt.PresupLemmas.
Require Import Setoid.
Require Import Coq.Program.Equality.



Lemma ctx_eq_refl (Γ : Ctx) : ⊢ Γ ->  ⊢ Γ ≈ Γ.
Proof.
  intro.
  induction H;mauto.
Qed.

Lemma ctx_eq_trans (Γ Δ Δ' : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Δ ≈ Δ' -> ⊢ Γ ≈ Δ'.
Proof.
  intros.
  generalize dependent Δ'.
  induction H.
  - intros.
    auto.
  - intros.
    inversion H4.
    destruct (lift_tm_max _ _ _ _ i i0 H0 H9).
    destruct (lift_eq_max _ _ _ _ _ _ i i0 H2 H10).
    destruct (lift_eq_max _ _ _ _ _ _ i i0 H3 H12).
    econstructor;mauto.
    -- eapply (ctxeq_eq _ _ _ _ _ (ctx_eq_sym _ _ H)).
       mauto.
    -- eapply (ctxeq_eq _ _ _ _ _ H7).
       mauto.    
Qed.



Add Parametric Relation : (Ctx) (wf_ctx_eq)
    symmetry proved by ctx_eq_sym
    transitivity proved by ctx_eq_trans
    as ctx_eq.

Add Parametric Relation (Γ : Ctx) (T : Typ) : (exp) (λ t t',wf_term_eq Γ t t' T)
    symmetry proved by (λ t t',wf_eq_sym Γ t t' T)
    transitivity proved by (λ t t' t'', wf_eq_trans Γ t t' T t'')
    as tm_eq.                                                

Add Parametric Relation (Γ Δ : Ctx) : (Sb) (λ σ τ, wf_sub_eq Γ σ τ Δ)
    symmetry proved by (λ σ τ, wf_sub_eq_sym Γ σ τ Δ)
    transitivity proved by (λ σ τ ρ, wf_sub_eq_trans Γ σ τ Δ ρ)
    as sb_eq.
