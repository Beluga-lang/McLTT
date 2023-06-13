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

Lemma presup_tm (Γ : Ctx) (t : exp) (T : Typ) (g_tm : Γ ⊢ t : T) :  ⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i
with presup_eq  (Γ : Ctx) (s t : exp) (T : Typ) (g_eq : Γ ⊢ s ≈ t : T) :  ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i,Γ ⊢ T : typ i
with presup_sb_eq (Γ Δ : Ctx) (σ τ : Sb) (g_seq : Γ ⊢s σ ≈ τ : Δ) : ⊢ Γ ∧ Γ ⊢s σ : Δ ∧ Γ ⊢s τ : Δ ∧ ⊢ Δ.                        
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
       
    -- pose proof (presup_tm _ _ _ H) as [NG _].
       pose proof (presup_tm _ _ _ H0) as [G ].
       mauto.
    --  pose proof presup_sb_ctx _ _ _ H as [G D].
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
       convert_to_relational.
       symmetry.
       convert_from_relational.
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
    -- pose proof (presup_tm _ _ _ H) as [NG _].
       pose proof (presup_eq _ _ _ _ H0) as [? [? [? _]]].
       pose proof (presup_eq _ _ _ _ H1) as [? [? [? _]]].
       pose proof (presup_eq _ _ _ _ H2) as [? [? [? _]]].
       pose proof (presup_eq _ _ _ _ H3) as [? [? [? _]]].
       assert (Γ ⊢s (a_id,, t0) : ℕ :: Γ) by (econstructor;mauto).
       breakdown_goal.
       assert (Γ ⊢ a_sub T0 (a_id,, a_zero) ≈ a_sub T' (a_id,,a_zero) : typ i).
       {
         assert (Γ ⊢s (a_id,, a_zero) : ℕ :: Γ) by (econstructor;mauto;(eapply wf_conv;mauto)).
         eapply wf_eq_conv.
         eapply wf_eq_sub_cong;mauto.
         mauto.
       }
       assert (Γ ⊢ a_sub T0 (a_id,, t0) ≈ a_sub T' (a_id,,t') : typ i).
       {
         
         eapply wf_eq_conv.
         eapply wf_eq_sub_cong;mauto.
         - econstructor;mauto.
         - econstructor;mauto.
       }  
       assert (T' :: ℕ :: Γ ⊢ a_sub T0 (a_weaken ∙ a_weaken,,a_succ (a_var 1)) ≈ a_sub T' (a_weaken ∙ a_weaken,,a_succ (a_var 1)): typ i).
       {
         enough (T' :: ℕ :: Γ ⊢s (a_weaken ∙ a_weaken ,, a_succ (a_var 1)) : ℕ :: Γ) as SBE.
         - eapply wf_eq_conv.
           eapply wf_eq_sub_cong;mauto.
           mauto.
         - assert (T' :: ℕ :: Γ ⊢ ℕ ≈ a_sub ℕ (a_weaken ∙ a_weaken) : typ i).
           {
             convert_to_relational.
             symmetry.
             erewrite rew_tm_nat_sub.
             all : convert_from_relational;mauto.
           }        
           econstructor;mauto.
           convert_to_relational.
           rewrite <- H23.
           econstructor.
           eapply wf_conv.
           econstructor;mauto.
           assert (ℕ :: Γ ⊢s a_weaken : Γ) by mauto.
           assert (T' :: ℕ :: Γ ⊢s a_weaken ∙ a_weaken : Γ) by mauto.
           convert_to_relational.
           transitivity (a_sub ℕ (a_weaken ∙ a_weaken)).
           eapply wf_eq_conv.
           convert_to_relational.
           symmetry.
           eapply wf_eq_sub_comp;mauto.
           eapply wf_eq_typ_sub;mauto.
           mauto.
           convert_from_relational.
           mauto.
       }    
       assert (⊢ T' :: ℕ :: Γ ≈ T0 :: ℕ :: Γ) by mauto using ctx_eq_refl.
       convert_to_relational.
       rewrite -> H22.
       econstructor;mauto.


       
    -- pose proof (presup_sb_ctx _ _ _ H) as [G D].
       pose proof (presup_tm _ _ _ H1) as [_ [? ?]].
       pose proof (presup_tm _ _ _ H2) as [? [? ?]].
       assert (Δ ⊢s (a_id,,t0) : ℕ :: Δ) by (econstructor;mauto).
       assert (Γ ⊢s a_id : Γ) by mauto.
       assert (Γ ⊢ ℕ : typ i) by mauto.
       assert (Δ ⊢ t0 : a_sub ℕ a_id) by mauto.
       assert (Γ ⊢s (a_id ,, t0) ∙ σ ≈ ((a_id ∙ σ) ,, (a_sub t0 σ)) : ℕ :: Δ) by mauto.
       assert (Γ ⊢s ((a_id ∙ σ) ,, (a_sub t0 σ)) ≈ (σ,,(a_sub t0 σ)) : ℕ :: Δ).
       {
         econstructor.
         mauto.
         mauto.
         mauto.
         eapply tm_eq_refl.
         assert (Γ ⊢ a_sub ℕ (a_id ∙ σ) ≈ ℕ : typ i) by mauto.
         assert (Γ ⊢ a_sub ℕ σ ≈ ℕ : typ i) by mauto.
         convert_to_relational.
         rewrite H16.
         rewrite <- H17.
         convert_from_relational.
         mauto.
       }  
       breakdown_goal.
       econstructor.
       econstructor.
       mauto.
       mauto.
       eapply wf_eq_conv.
       assert (Γ ⊢ a_sub T0 ((a_id,, t0) ∙ σ) ≈ a_sub (a_sub T0 (a_id,, t0)) σ : typ i).
       {
         eapply wf_eq_conv.         
         eapply wf_eq_sub_comp;mauto.
         mauto.
       }
       convert_to_relational.
       rewrite H16 in H15.
       symmetry.
       rewrite <- H17.
       eapply wf_eq_conv.
       eapply wf_eq_sub_cong;mauto.
       mauto.
       mauto.

       assert (ℕ :: Γ ⊢ (ℕ ⟦ σ ∙ a_weaken ⟧) ≈ (ℕ ⟦ a_weaken ⟧) : typ i).
       {
         convert_to_relational.
         autorewrite with mcltt_types.
         all: convert_from_relational;mauto.
       }
       econstructor.
       econstructor.
       econstructor.
       econstructor.
       econstructor.
       mauto.
       eapply wf_univ_nat_f;mauto.
       
       convert_to_relational.
       erewrite H17.
       convert_from_relational.
       econstructor;mauto.
       mauto.
       eapply wf_eq_typ_sub.
       econstructor.
       econstructor.
       mauto.
       mauto.
       eapply wf_univ_nat_f;mauto.
       
       eapply wf_conv.
       econstructor;mauto.
       convert_to_relational.
       erewrite H17.
       convert_from_relational.
       mauto.

       econstructor.
       econstructor.
       mauto.
       mauto.
       eapply wf_eq_conv.
       convert_to_relational.
       autorewrite with mcltt.
       1-3: convert_from_relational;mauto.
       assert (Γ ⊢s (a_id,, a_zero) ∙ σ ≈ (σ ,, a_zero) : ℕ :: Δ).
       {
         convert_to_relational.
         erewrite rew_sb_ext_comp.
         eapply wf_sub_eq_ext_cong;mauto.
         eapply wf_eq_conv.
         mauto.
         mauto.
         all: convert_from_relational;mauto.
         eapply wf_conv;mauto.
       }
       convert_to_relational.
       symmetry.
       transitivity ((T0 ⟦ (a_id,,a_zero) ∙ σ ⟧)).
       symmetry.
       transitivity (T0 ⟦ var_wk σ ∙ (a_id,,a_zero)⟧).
       1-3: convert_from_relational.
       eapply wf_eq_conv.
       eapply wf_eq_sub_cong.
       mauto.
       convert_to_relational.
       rewrite H18.
       econstructor.
       eapply here.
       admit.
       (*eapply wf_conv.
       eapply wf_nat_elim.
       eapply wf_conv.
       econstructor.
       econstructor.
       econstructor.
       mauto.
       mauto.
       eapply (wf_univ_nat_f _ _ D).
       eapply wf_conv.
       mauto.
       transitivity ℕ.
       mauto.
       symmetry;mauto.
       mauto.
       eapply wf_eq_typ_sub.
       econstructor;mauto.
       eapply wf_conv.
       econstructor;mauto.
       
       
       eapply wf_conv.
       econstructor.
       econstructor.
       econstructor.
       mauto.
       mauto.
       mauto. *)
       exists i.
       mauto.
    -- pose proof (presup_tm _ _ _ H) as [NG _].
       pose proof (presup_tm _ _ _ H0) as [G [? ?]].
       pose proof (presup_tm _ _ _ H1) as [TNG [? ?]].
       breakdown_goal.
    --  pose proof (presup_tm _ _ _ H) as [NG _].
       pose proof (presup_tm _ _ _ H0) as [G [? ?]].
       pose proof (presup_tm _ _ _ H1) as [TNG [? ?]].
        assert ( Γ ⊢s (a_id,, t0) : ℕ :: Γ) by (econstructor;mauto). 
       breakdown_goal.
       eapply wf_conv.
       econstructor.
       2 : exact H1.
       econstructor.
       econstructor;mauto.
       eapply wf_conv;mauto.
       eapply wf_conv.
       econstructor.
       mauto.
       mauto.
       mauto.
      
       eapply tm_eq_refl.
       eapply wf_conv;mauto.
       eapply wf_eq_conv.
       transitivity (a_sub T0 ((a_weaken ∙ a_weaken,, a_succ (a_var 1)) ∙ (((a_id,, t0),, a_rec T0 s0 r t0)))).
       symmetry.
       eapply wf_eq_sub_comp.
       econstructor;mauto.
       econstructor.
       econstructor.
       mauto.
       mauto.
       eapply (wf_univ_nat_f _ _ G).
       assert (T0 :: ℕ :: Γ ⊢ a_sub ℕ (a_weaken ∙ a_weaken) ≈ ℕ : typ i) by mauto.
       rewrite H10.
       econstructor.
       eapply wf_conv;mauto.
       transitivity (a_sub ℕ (a_weaken ∙ a_weaken)).
       eapply wf_eq_conv.
       symmetry.
       eapply wf_eq_sub_comp;mauto.
       mauto.
       mauto.
       mauto.

       eapply wf_eq_sub_cong.
       mauto.
       erewrite (wf_sub_eq_ext_comp).
       eapply wf_sub_eq_ext_cong.
       erewrite (wf_sub_eq_comp_assoc).
       assert (Γ ⊢s (a_weaken ∙ ((a_id,, t0),, a_rec T0 s0 r t0)) ≈ (a_id,,t0) : ℕ :: Γ) by (erewrite -> (wf_sub_eq_p_ext);mauto).
       assert (Γ ⊢s a_weaken ∙ (a_id,,t0) ≈ a_id : Γ).
       {
         erewrite (wf_sub_eq_p_ext).
         mauto.
         mauto.
         eapply (wf_univ_nat_f _ _ G).
         mauto.
       }
       transitivity ( a_weaken ∙ (a_id,, t0)).
       eapply wf_sub_eq_comp_cong;mauto.
       mauto.
       mauto.
       mauto.
       econstructor.
       mauto.
       mauto.
       mauto.
       mauto.

       1-7: admit.
       
    -- pose proof (presup_tm _ _ _ H) as [G _].
       pose proof (presup_eq _ _ _ _ H0) as [MG [? [? [x ?]]]].
       breakdown_goal.
       pose proof (ctx_decomp _ _ MG) as [_ [n ?]].
       exists (max x n).
       destruct (lift_tm_max _ _ _ _ _ _ H7 H8).
       mauto.
    -- pose proof (presup_eq _ _ _ _ H1) as [G [Gr [Gr' [n GPi]]]].
       pose proof (presup_eq _ _ _ _ H2) as [_ [Gm [Gm' _]]].
       breakdown_goal.
       econstructor.
       econstructor.
       exact H.
       exact H0.
       exact Gr'.
       exact Gm'.
       eapply wf_eq_conv.
       eapply wf_eq_sub_cong.
       eapply tm_eq_refl;mauto.
       econstructor;mauto.
       eapply wf_eq_typ_sub.
       econstructor;mauto.
       eapply wf_conv.
       exact Gm'.
       
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

#[export]
Hint Resolve presup_tm presup_eq presup_sb_eq : mcltt.
