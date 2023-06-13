Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.

Open Scope mcltt.

Lemma ctxeq_tm (Γ Δ : Ctx) (t : exp) (T : Typ) : ⊢ Γ ≈ Δ -> Γ ⊢ t : T -> Δ ⊢ t : T
with
ctxeq_eq (Γ Δ : Ctx) (t t' : exp) (T : Typ) : ⊢ Γ ≈ Δ -> Γ ⊢ t ≈ t' : T -> Δ ⊢ t ≈ t' : T
with
ctxeq_s (Γ Γ' Δ : Ctx) (σ : Sb) : ⊢ Γ ≈ Δ -> Γ ⊢s σ : Γ' -> Δ ⊢s σ : Γ'
with
ctxeq_s_eq (Γ Γ' Δ : Ctx) (σ σ' : Sb) : ⊢ Γ ≈ Δ -> Γ ⊢s σ ≈ σ' : Γ' -> Δ ⊢s σ ≈ σ' : Γ'.
Proof.
  (*ctxeq_tm*)
  - clear ctxeq_tm.
    intros.
    generalize dependent Δ.
    induction H0;intros;try destruct (presup_ctx_eq _ _ H0);mauto.
    -- destruct (presup_ctx_eq _ _ H) as [G D].
       pose proof (IHwf_term1 _ H).
       assert (⊢ a :: Γ ≈ a :: Δ) by mauto.
       mauto.
    -- destruct (presup_ctx_eq _ _ H) as [G D].
       pose proof (IHwf_term1 _ H).
       assert (⊢ A :: Γ ≈ A :: Δ) by mauto.
       mauto.       
    -- destruct (var_in_eq _ _ _ x H1 H0) as [T' [i [xT'G [GTT' DTT']]]].
       mauto.
    -- destruct (presup_ctx_eq _ _ H) as [G D].
       assert (⊢ A :: Γ ≈ A :: Δ) by mauto 6 using tm_eq_refl.
       econstructor;mauto.
    -- pose proof (IHwf_term1 _ H).
       assert (⊢ A :: Γ ≈ A :: Δ) by mauto.
       mauto.
    -- assert (⊢ ℕ :: Γ ≈ ℕ :: Δ) by (econstructor;mauto).
       pose proof (IHwf_term1 _ H0).
       pose proof (IHwf_term2 _ H).
       assert (⊢ T :: ℕ :: Γ ≈ T :: ℕ :: Δ) by (econstructor;mauto).
       pose proof (IHwf_term3 _ H3).
       mauto.
  (*ctxeq_eq*)
  - clear ctxeq_eq.
    intros.
    generalize dependent Δ.
    induction H0.
    1-3: mauto.
    4-6: mauto.
    10-15,20-23: mauto.
    -- intros.
       pose proof (IHwf_term_eq1 _ H0).
       pose proof (ctxeq_tm _ _ _ _ H0 H).
       assert (⊢ M :: Γ ≈ M :: Δ) by mauto.
       mauto.
    -- intros.
       destruct (presup_ctx_eq _ _ H1) as [G D].
       pose proof (var_in_eq _ _ _ _ H1 H0) as [T' [n [xT' [GTT' DTT']]]].
       eapply wf_eq_conv;mauto.
    -- intros.
       destruct (presup_ctx_eq _ _ H0) as [G D].
       mauto.

    -- intros.
       assert (⊢ ℕ :: Γ ≈ ℕ :: Δ) by (econstructor;mauto).
       pose proof (IHwf_term_eq1 _ H1).
       pose proof (IHwf_term_eq2 _ H0).
       pose proof (IHwf_term_eq4 _ H0).
       assert (⊢ T :: ℕ :: Γ ≈ T :: ℕ :: Δ) by (econstructor;mauto).
       pose proof (IHwf_term_eq3 _ H5).
       mauto.
    -- intros.
       mauto.
    -- intros.
       assert (⊢ ℕ :: Γ ≈ ℕ :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H3 H).
       pose proof (ctxeq_tm _ _ _ _ H2 H0).
       assert (⊢ T :: ℕ :: Γ ≈ T :: ℕ :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H6 H1).
       mauto.
    -- intros.
       assert (⊢ ℕ :: Γ ≈ ℕ :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H4 H).
       pose proof (ctxeq_tm _ _ _ _ H3 H0).
       pose proof (ctxeq_tm _ _ _ _ H3 H2).
       assert (⊢ T :: ℕ :: Γ ≈ T :: ℕ :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H8 H1).
       mauto.
    -- intros.
       assert (⊢ M :: Γ ≈ M :: Δ) by (econstructor;mauto).
       pose proof (IHwf_term_eq _ H2).
       mauto.
    -- intros.
       pose proof (IHwf_term_eq1 _ H1).
       pose proof (IHwf_term_eq2 _ H1).
       pose proof (ctxeq_tm _ _ _ _ H1 H).
       assert (⊢ M :: Γ ≈ M :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H5 H0).
       mauto.
    -- intros.
       inversion H1.
       pose proof (var_in_eq _ _ _ x H4 H0) as [T'' [n [xT'' [GTT'' DTT'']]]].
       destruct (presup_ctx_eq _ _ H4).
       eapply wf_eq_conv;mauto.
    -- intros.
       mauto.
    -- intros.
       mauto.
    -- intros.
       pose proof (ctxeq_tm _ _ _ _ H3 H).
       assert (⊢ M :: Γ ≈ M :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H5 H0).
       pose proof (ctxeq_tm _ _ _ _ H5 H1).
       mauto.
    -- intros.
       pose proof (ctxeq_tm _ _ _ _ H2 H).
       pose proof (ctxeq_tm _ _ _ _ H2 H1).
       assert (⊢ M :: Γ ≈ M :: Δ) by (econstructor;mauto).
       pose proof (ctxeq_tm _ _ _ _ H5 H0).
       mauto.
  (*ctxeq_s*)
  - clear ctxeq_s.
    intros.
    destruct (presup_ctx_eq _ _ H).
    induction H0;mauto.
    -- inversion H.
       rewrite <- H9 in H,H2.
       mauto.
  (*ctxeq_s_eq*)
  - clear ctxeq_s_eq. 
    intros.
    destruct (presup_ctx_eq _ _ H).
    induction H0.
    3-7,11-13 : mauto.   
    -- eapply wf_sub_eq_conv.
       eapply (wf_sub_eq_id _ H2).
       mauto.
    -- inversion H.
       rewrite <- H9 in H2.
       eapply wf_sub_eq_conv;mauto. 
    -- pose proof (ctxeq_s _ _ _ _ H H5).
       mauto.
    -- pose proof (ctxeq_s _ _ _ _ H H0).
       pose proof (ctxeq_tm _ _ _ _ H H4).
       mauto.
    -- pose proof (ctxeq_s _ _ _ _ H H0).
       mauto.

       Unshelve.
       1-4: exact 0.
Qed.  

#[export]
Hint Resolve ctxeq_tm ctxeq_eq ctxeq_s ctxeq_s_eq : mcltt.


