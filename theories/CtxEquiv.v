Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.

Lemma ctxeq_tm : forall {Γ Δ t T}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ t : T }} -> {{ Δ ⊢ t : T }}
with
ctxeq_eq : forall {Γ Δ t t' T}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ t ≈ t' : T }} -> {{ Δ ⊢ t ≈ t' : T }}
with
ctxeq_s : forall {Γ Γ' Δ σ}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}
with
ctxeq_s_eq : forall {Γ Γ' Δ σ σ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof with mauto.
  (*ctxeq_tm*)
  - clear ctxeq_tm.
    intros * HΓΔ Ht.
    gen Δ.
    induction Ht; intros; destruct (presup_ctx_eq HΓΔ)...
    -- pose proof (IHHt1 _ HΓΔ).
       assert ({{ ⊢ Γ , A ≈ Δ , A }})...
    -- destruct (var_in_eq HΓΔ H0) as [T' [i [xT'G [GTT' DTT']]]].
       eapply wf_conv...
    -- assert ({{ ⊢ Γ , A ≈ Δ , A }}); mauto 6.
    -- pose proof (IHHt1 _ HΓΔ).
       assert ({{ ⊢ Γ , A ≈ Δ , A }})...
  (*ctxeq_eq*)
  - clear ctxeq_eq.
    intros * HΓΔ Htt'.
    gen Δ.
    induction Htt'; intros; destruct (presup_ctx_eq HΓΔ).
    1-4,6-19: mauto.
    -- pose proof (IHHtt'1 _ HΓΔ).
       pose proof (ctxeq_tm _ _ _ _ HΓΔ H).
       assert ({{ ⊢ Γ , M ≈ Δ , M }})...
    -- inversion_clear HΓΔ.
       pose proof (var_in_eq H3 H0) as [T'' [n [xT'' [GTT'' DTT'']]]].
       destruct (presup_ctx_eq H3).
       eapply wf_eq_conv...
    -- pose proof (var_in_eq HΓΔ H0) as [T'' [n [xT'' [GTT'' DTT'']]]].
       eapply wf_eq_conv...
  (*ctxeq_s*)
  - clear ctxeq_s.
    intros * HΓΔ Hσ.
    gen Δ.
    induction Hσ; intros; destruct (presup_ctx_eq HΓΔ)...
    inversion_clear HΓΔ.
    econstructor...
  (*ctxeq_s_eq*)
  - clear ctxeq_s_eq.
    intros * HΓΔ Hσσ'.
    gen Δ.
    induction Hσσ'; intros; destruct (presup_ctx_eq HΓΔ).
    3-9,11-13: mauto.
    -- inversion_clear HΓΔ; eapply wf_sub_eq_conv...
    -- inversion_clear HΓΔ; eapply wf_sub_eq_conv...
    -- econstructor. eapply ctxeq_s...
Qed.

#[export]
Hint Resolve ctxeq_tm ctxeq_eq ctxeq_s ctxeq_s_eq : mcltt.
