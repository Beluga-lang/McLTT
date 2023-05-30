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

Lemma inv_pi (Γ : Ctx) (M T T' : Typ) : Γ ⊢ Π M T : T' -> ∃ i,M :: Γ ⊢ T : typ i.
Proof.
  intros.
  dependent induction H;mauto.  
Qed.


(*
Add Parametric Morphism (Γ Δ : Ctx) : (λ σ, wf_sb Γ σ Δ)
    with signature (λ σ τ, wf_sub_eq Γ σ τ Δ) ==> iff as sb_mor.
Proof.
  intros.
  split.
  intro.
  generalize dependent y.
  induction H0.
  intros.
  inversion H0.
  mauto.
  rewrite <- H5 in H.
  pose proof (ctx_decomp _ _ H) as [_ [i GT]].
  econstructor.
  econstructor.
  econstructor.
  exact H.
  econstructor.
  exact H.
  exact GT.

  econstructor.
  mauto.
  eapply wf_eq_conv;mauto.

  
  
  dependent induction H0.
  dependent induction H.
  mauto.
  
  econstructor.
  mauto.
  mauto.
  eapply wf_conv.
  econstructor.
  exact H.
  econstructor.
  exact H0.
  eapply here.
  eapply wf_eq_conv.
  mauto.
  mauto.

  
  admit.

  eapply IHwf_sub_eq2.
  symmetry.
  
  
Qed.  

                           
Add Parametric Morphism (Γ : Ctx) (T : Typ) : (λ t,@wf_term Γ t T)
  with signature (λ t s,wf_term_eq Γ t s T ) ==> iff as tm_mor.                                   
Proof.
  intros.
  
Qed.

*)
