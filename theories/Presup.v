Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.
Require Import Mcltt.CtxEquiv.
Require Import Mcltt.PresupLemmas.
Require Import Mcltt.Relations.
Require Import Setoid.

Ltac breakdown_goal :=
  let rec splitting :=
    match goal with
    | [H : _ |- ?X ∧ ?Y] => split;splitting
    | [H : _ |- _ ] => mauto
    end
  in splitting
.

Fixpoint presup_tm (Γ : Ctx) (t : exp) (T : Typ) (g_tm : Γ ⊢ t : T) {struct g_tm}:  ⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i
with presup_eq  (Γ : Ctx) (s t : exp) (T : Typ) (g_eq : Γ ⊢ s ≈ t : T) {struct g_eq} :  ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i,Γ ⊢ T : typ i
with presup_sb_eq (Γ Δ : Ctx) (σ τ : Sb) (g_seq : Γ ⊢s σ ≈ τ : Δ) {struct g_seq} : ⊢ Γ ∧ Γ ⊢s σ : Δ ∧ Γ ⊢s τ : Δ ∧ ⊢ Δ.                        
Proof.
  - inversion g_tm;clear g_tm.
    1-4,8-9 : mauto.
    -- pose proof (wf_vlookup _ _ _ H H0).
       breakdown_goal.
    -- pose proof presup_tm _ _ _ H0 as [AG [i0 AGi]].
       pose proof ctx_decomp _ _ AG as [G [i1 GTi1]].
       breakdown_goal.
       exists i.
       eapply (sub_lvl _ _ _ _ _ H0).
       econstructor;mauto.

    -- pose proof presup_tm _ _ _ H as [G [i0 GAi]].
       pose proof presup_tm _ _ _ H0 as [AG [i1 AGi1]].
       breakdown_goal.
       exists (max i i1).
       pose proof (lift_tm_max _ _ _ _ _ _ H AGi1) as [Ga AGB].
       econstructor;auto.
       
    -- pose proof presup_sb_ctx _ _ _ H as [G D].
       pose proof presup_tm _ _ _ H0 as [_ [i0 DAi0]].
       breakdown_goal.
    -- pose proof presup_eq _ _ _ _ H0 as [G [_ [GT _]]].
       breakdown_goal.
    -- pose proof presup_tm_ctx _ _ _ H.
       breakdown_goal.
       
  - inversion g_eq;clear g_eq.    
    -- pose proof presup_sb_ctx _ _ _ H as [G D].
       clear presup_eq.
       breakdown_goal.

    -- pose proof presup_sb_ctx _ _ _ H as [G D].
       clear presup_eq.
       breakdown_goal.

    -- pose proof presup_sb_ctx _ _ _ H as [G D].
       pose proof (wf_pi _ _ _ _ H0 H1).
       breakdown_goal.
       econstructor;mauto.
       eapply (sub_lvl _ _ _ _ _ H1).
       econstructor.
       econstructor;mauto.
       mauto.
       eapply wf_conv;mauto.
       eapply wf_eq_conv.
       eapply wf_eq_sym.
       eapply wf_eq_sub_comp;mauto.
       eapply wf_eq_typ_sub;mauto.   

    -- pose proof (presup_eq _ _ _ _ H0) as [G [GM [GM' _]]].
       pose proof (presup_eq _ _ _ _ H1) as [MG [MGT0 [MGT' _]]].
       clear presup_eq.
       breakdown_goal.
       econstructor;mauto.
       eauto using ctxeq_tm, ctx_eq_refl with mcltt.

    -- breakdown_goal.

    -- breakdown_goal.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       breakdown_goal.

    -- pose proof (presup_eq _ _ _ _ H) as [G [Gt0 [Gt' GTi]]].
       breakdown_goal.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       breakdown_goal.

    -- pose proof (presup_sb_eq _ _ _ _ H0) as [G [Gs [Gs' D]]].
       pose proof (presup_eq _ _ _ _ H) as [_ [Dt0 [Dt' [i DT0i]]]].
       breakdown_goal.
       econstructor;mauto.
       eapply wf_eq_conv;mauto using wf_eq_sub_cong.

    -- pose proof (presup_tm _ _ _ H) as [G [i GTi]].
       breakdown_goal.

    -- pose proof (ctx_decomp _ _ H) as [G0 [i G0M]].
       breakdown_goal.

    -- pose proof (presup_tm _ _ _ H1) as [_ [i ]].
       breakdown_goal.
       econstructor;mauto.
       eapply wf_eq_conv.
       eapply wf_eq_sym.
       eapply wf_eq_sub_comp;mauto.
       mauto.

    -- pose proof (presup_tm _ _ _ H1) as [G [n ]].
       breakdown_goal.
       eapply wf_conv.
       eapply wf_sub;mauto.
       eapply wf_eq_trans.
       eapply wf_eq_sym.
       eapply wf_eq_conv.
       eapply wf_eq_sub_comp;mauto.
       econstructor;mauto.
       econstructor;mauto.
       econstructor;mauto.
       econstructor;mauto.
       econstructor;mauto.
       econstructor;mauto.     

    -- breakdown_goal.
       eapply wf_conv.
       eapply wf_sub;mauto.
       eapply wf_eq_conv.
       eapply wf_eq_trans.
       eapply wf_eq_sym.
       eapply wf_eq_conv.
       eapply wf_eq_sub_comp;mauto.
       eapply wf_eq_typ_sub.
       econstructor;mauto.
       eapply wf_eq_conv.
       eapply wf_eq_sub_cong;mauto.
       eapply wf_eq_typ_sub.
       econstructor;mauto.
       mauto.

    -- pose proof (presup_eq _ _ _ _ H) as [G [Gs [Gt _]]].
       breakdown_goal.

    -- pose proof (presup_eq _ _ _ _ H) as [G [Gs [Gt [n GT0]]]].
       pose proof (presup_eq _ _ _ _ H0) as [_ [_ [GT _]]].
       breakdown_goal.

    -- pose proof (presup_eq _ _ _ _ H) as [G [Gt [Gs [n GTn]]]].
       breakdown_goal.
       
    -- pose proof (presup_eq _ _ _ _ H) as [G [Gs [Gt' [n GTn]]]].
       pose proof (presup_eq _ _ _ _ H0) as [_ [_ [Gt _]]].
       breakdown_goal.

  - inversion g_seq;clear g_seq.
    -- breakdown_goal.
       
    -- pose proof (ctx_decomp _ _ H) as [D [i DTi]].
       breakdown_goal.

    -- pose proof (presup_sb_eq _ _ _ _ H) as [G [Gt0 [Gt' G']]].
       pose proof (presup_sb_eq _ _ _ _ H0) as [_ [G's0 [G's' D]]].
       breakdown_goal.

    -- pose proof (presup_sb_eq _ _ _ _ H) as [G [Gs0 [Gs' D0]]].
       pose proof (presup_eq _ _ _ _ H1) as [_ [Gt [Gt' [n _]]]].
       breakdown_goal.
       econstructor;mauto.
       eapply (wf_conv _ _ _ _ _ Gt').
       eapply wf_eq_conv.
       eapply wf_eq_sub_cong;mauto.
       mauto.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       breakdown_goal.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       breakdown_goal.
       
    -- pose proof (presup_sb_ctx _ _ _ H) as [G' D].
       pose proof (presup_sb_ctx _ _ _ H0) as [G'' _].
       breakdown_goal.

    -- breakdown_goal.
       econstructor.
       econstructor;mauto.
       mauto.
       eapply wf_conv.
       eapply (wf_sub _ _ _ _ _ H2 H1).
       eapply wf_eq_conv.
       eapply wf_eq_sym.
       eapply wf_eq_sub_comp;mauto.
       mauto.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       breakdown_goal.

    -- pose proof (presup_sb_ctx _ _ _ H) as [G TG0].
       pose proof (ctx_decomp _ _ TG0) as [G0 [i G0T]].
       clear presup_sb_eq.
       breakdown_goal.
       econstructor;mauto.
       eapply wf_conv;mauto.
       mauto.
       eapply wf_eq_conv;mauto.

    -- pose proof (presup_sb_eq _ _ _ _ H) as [G [Gt [Gs D]]].
       breakdown_goal.

    -- pose proof (presup_sb_eq _ _ _ _ H) as [G [Gs [Gs' D]]].
       pose proof (presup_sb_eq _ _ _ _ H0) as [_ [_ [Gt _]]].
       breakdown_goal.

    -- pose proof (presup_sb_eq _ _ _ _ H) as [G [Gs [Gt _]]].
       pose proof (presup_ctx_eq _ _ H0) as [D0 D].
       breakdown_goal.
    Unshelve.
    1-9: exact 0. 
Qed.  
