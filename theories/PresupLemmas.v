Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Export Lia.

Lemma ctx_decomp (Γ : Ctx) (T : Typ) : ⊢ T :: Γ -> (⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  destruct H.
  (* Using either destruct or induction on H forces us to consider a case where H : ⊢ nil, which doesn't make sense
     and so we can't really prove anything for it. *)
  admit.
  (* If we then skip that problematic case, the information we get from destructing H doesn't actually apply
     because it refers to fresh instances of Γ and T for some reason *)
Admitted.

(* Corresponds to presup-⊢≈ in the Agda proof*)
Lemma presup_ctx_eq (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Γ ∧ ⊢ Δ.
Proof.
  intro.
  induction H.
  - split; exact wf_empty.
  - destruct IHwf_ctx_eq.
    split.
    -- apply (wf_extend _ _ _ H5 H0).
    -- apply (wf_extend _ _ _ H6 H1).   
Qed.
(* Corresponds to ≈-refl in the Agda code*)
Lemma tm_eq_refl (Γ : Ctx) (t: exp) (T : Typ) : Γ ⊢ t : T -> Γ ⊢ t ≈ t : T.
Proof.
  intros.
  exact (wf_eq_trans _ _ _ _ _ (wf_eq_sym _ _ _ _ (wf_eq_sub_id _ _ _ H)) (wf_eq_sub_id _ _ _ H)).
Qed.

Lemma sb_eq_refl (Γ Δ : Ctx) (σ : Sb) : Γ ⊢s σ : Δ -> Γ ⊢s σ ≈ σ : Δ.
Proof.
  intros.
  pose proof (wf_sub_eq_id_comp_right _ _ _ H).
  pose proof (wf_sub_eq_sym _ _ _ _ H0).
  exact (wf_sub_eq_trans _ _ _ _ _ H1 H0).
Qed.


Lemma presup_tm (Γ : Ctx) (t : exp) (T : Typ) : Γ ⊢ t : T -> ⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i.
Proof.
   assert (presup_sb : ∀ Γ Δ σ, Γ ⊢s σ : Δ -> ⊢ Γ ∧ ⊢ Δ) by admit.
  assert (presup_tm_eq : ∀ Γ s t T,  (Γ ⊢ s ≈ t : T) -> ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i, Γ ⊢ T : typ i) by admit.
  intro.
  induction H.
  - split;auto.
    exists (i+1).
    constructor;auto.

  - split;auto.
    exists (i + 1 + 1).
    constructor;auto.

  - destruct IHwf_term1.
    destruct IHwf_term2.
    split;auto.
    
  - destruct IHwf_term1.
    destruct IHwf_term2.
    split;auto.

  - split;auto.
    pose proof (wf_vlookup _ _ _ H H0).
    induction H0.
    -- destruct (ctx_decomp _ _ H).
       destruct H2.
       pose proof (wf_sb_weaken _ _ H).
       pose proof (wf_sub _ _ _ _ _ H3 H2).
       exists x.
       apply (wf_conv _ _ _ _ (x+1) H4).
       exact (wf_eq_typ_sub _ _ _ _ H3).

    -- destruct (ctx_decomp _ _ H).
       destruct H3.
       pose proof (wf_vlookup _ _ _ H2 H0).
       destruct (IHctx_lookup H2 H4).
       pose proof (wf_sb_weaken _ _ H).
       pose proof (wf_sub _ _ _ _ _ H6 H5).
       exists x0.
       apply (wf_conv _ _ _ _ (x0+1) H7).
       exact (wf_eq_typ_sub _ _ _ _ H6).

  - destruct IHwf_term1.
    destruct IHwf_term2.
    destruct IHwf_term3.
    split;auto.
    pose proof (wf_sb_id _ H2).
    destruct H5.
    pose proof (wf_sub _ _ _ _ _ H8 H0).
    assert (Γ ⊢ N : a_sub A a_id).
    {
      apply (wf_conv _ _ _ _ x H0).
      apply (wf_eq_sym).
      exact (wf_eq_sub_id _ _ _ H5).
    }  
    pose proof (wf_sb_extend _ _ _ _ _ _ H8 H5 H10).
    pose proof (wf_sub _ _ _ _ _ H11 H1).
    exists i.
    apply (wf_conv _ _ _ _ (i+1) H12).
    exact (wf_eq_typ_sub _ _ _ _ H11).

  - destruct IHwf_term1.
    destruct IHwf_term2.
    destruct H2.
    destruct H4.
    split;auto.

    (* Todo:
       This section can go through easily once I have some lemmas for lifting universe levels.
       For now I just force it past this step.
    *)
    assert (x0 = i) by admit.
    rewrite H5 in H4.
    exists i.
    exact (wf_pi _ _ _ _ H H4).
    (* End of forced section *)

  - split;auto.
    exists 1.
    constructor;auto.

  - destruct IHwf_term.
    split;auto.

  - destruct IHwf_term.
    split;auto.
    -- destruct (presup_sb _ _ _ H).
       exact H3.
    -- destruct H2.
       pose proof (wf_sub _ _ _ _ _ H H2).
       exists x.
       apply (wf_conv _ _ _ _ (x+1) H3).
       exact (wf_eq_typ_sub _ _ _ _ H).

  - destruct IHwf_term.
    split;auto.
    destruct (presup_tm_eq _ _ _ _ H0).
    destruct H4.
    destruct H5.
    eauto.

  - destruct IHwf_term.
    split;auto.
    destruct H1.
    exists(1 + i + 1).
    constructor;auto.
Admitted.  

Lemma presup_sb_eq (Γ Δ : Ctx) (σ τ: Sb) : Γ ⊢s σ ≈ τ : Δ -> ⊢ Γ ∧ ⊢ Γ ∧ Γ ⊢s σ : Δ ∧ Γ ⊢s τ : Δ.
Proof.
  assert (presup_sb : ∀ Γ Δ σ, Γ ⊢s σ : Δ -> ⊢ Γ ∧ ⊢ Δ) by admit.
  assert (presup_tm_eq : ∀ Γ s t T,  (Γ ⊢ s ≈ t : T) -> ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i, Γ ⊢ T : typ i) by admit.
  intros.
  induction H.

  - split;try constructor;auto.
    split;constructor;auto.

  - split;try split;auto.
    split; constructor;auto.

  - destruct IHwf_sub_eq1 as [G1 [G2 [GsT1 GsT2]]].
    destruct IHwf_sub_eq2 as [G1' [G2' [GsT1' GsT2']]].
    split;try split;auto.
    split.
    apply (wf_sb_compose Γ _ Γ' _ Γ'');auto.
    apply (wf_sb_compose Γ _ Γ' _ Γ'');auto.
  - destruct IHwf_sub_eq as [G1 [G2 [GsT1 GsT2]]].
    split;try split;auto.
    destruct (presup_tm_eq _ _ _ _ H1).
    destruct H3.
    split.
    -- exact (wf_sb_extend _ _ _ _ i _ GsT1 H0 H3).
    -- apply (wf_sb_extend _ _ _ _ i _ GsT2 H0).
       destruct H4.
       destruct H5.
       apply (wf_conv _ _ _ _ i H4).
       pose proof (tm_eq_refl _ _ _ H0).
       pose proof (wf_eq_sub_cong _ _ _ _ _ _ _ H6 H).
       apply (wf_eq_conv _ _ _ _ _ (i+1) H7).
       exact (wf_eq_typ_sub _ _ _ _ GsT1).
  
  - split;try split;auto.
    destruct (presup_sb _ _ _ H).
    auto.
    destruct (presup_sb _ _ _ H).
    auto.
    split;auto.
    apply (wf_sb_compose _ _ _ _ _ H).
    constructor.
    destruct (presup_sb _ _ _ H).
    auto.

  - destruct (presup_sb _ _ _ H).
    split;try split;auto.
    split.
    apply (wf_sb_compose _ _ _ _ _ (wf_sb_id _ H0) H).
    auto.

  - destruct (presup_sb _ _ _ H1).
    destruct (presup_sb _ _ _ H).
    split;try split;auto.
    split.
    -- pose proof (wf_sb_compose _ _ _ _ _ H0 H).
       exact (wf_sb_compose _ _ _ _ _ H1 H6).
    -- pose proof (wf_sb_compose _ _ _ _ _ H1 H0).
       exact (wf_sb_compose _ _ _ _ _ H6 H).
  
  - destruct (presup_sb _ _ _ H2).
    split;try split;auto.
    split.
    -- apply (wf_sb_compose _ _ _ _ _ H2).
       exact (wf_sb_extend _ _ _ _ _ _ H H0 H1).
    -- pose proof (wf_sb_compose _ _ _ _ _ H2 H).
       apply (wf_sb_extend _ _ _ _ i _ H5).
       auto.
       pose proof (wf_sub _ _ _ _ _ H2 H1).
       apply (wf_conv _ _ _ _ i H6).
       pose proof (wf_eq_sub_comp _ _ _ _ _ _ _ H2 H H0).
       pose proof (wf_eq_typ_sub _ _ _ i H5).
       pose proof (wf_eq_conv _ _ _ _ _ (i+1) H7 H8).
       exact (wf_eq_sym _ _ _ _ H9).
  
  - destruct (presup_sb _ _ _ H).
    split;try split;auto.
    split;auto.
    pose proof (wf_sb_extend _ _ _ _ _ _ H H0 H1).
    apply (wf_sb_compose _ _ _ _ _ H4).
    destruct (presup_sb _ _ _ H4).
    constructor.
    auto.

  - destruct (presup_sb _ _ _ H).
    auto.
    split;try split;auto.
    split; auto.
    destruct (ctx_decomp _ _ H1).
    destruct H3.
    apply (wf_sb_extend _ _ _ _ x _).
    apply (wf_sb_compose _ _ _ _ _ H).
    constructor.
    auto.
    auto.
    pose proof (here T Γ).
    pose proof (wf_vlookup _ _ _ H1 H4).
    pose proof (wf_sub _ _ _ _ _ H H5).
    apply (wf_conv _ _ _ _ x H6).
    apply (wf_eq_sym).
    pose proof (wf_sb_weaken _ _ H1).
    pose proof (wf_eq_sub_comp _ _ _ _ _ _ _ H H7 H3).
    apply (wf_eq_conv _ _ _ _ _ (x+1) H8).
    pose proof (wf_sb_compose _ _ _ _ _ H H7).
    exact (wf_eq_typ_sub _ _ _ x H9).

  - destruct IHwf_sub_eq as [G1 [G2 [GsT1 GsT2]]].
    split;try split;auto.
  
  - destruct IHwf_sub_eq1 as [G1 [G2 [GsT1 GsT2]]].
    destruct IHwf_sub_eq2 as [G1' [G2' [GsT1' GsT2']]].
    split; try split;auto.
    
  -  destruct IHwf_sub_eq as [G1 [G2 [GsT1 GsT2]]].
     split; try split;auto.
     split.
     exact (wf_sb_conv _ _ _ _ GsT1 H0).
     exact (wf_sb_conv _ _ _ _ GsT2 H0).
Admitted.  

Lemma presup_sb (Γ Δ: Ctx) (σ : Sb) : Γ ⊢s σ : Δ -> ⊢ Γ ∧ ⊢ Δ.
Proof.
  intros.
  induction H.
  - auto.
  - destruct (ctx_decomp _ _ H).
    destruct H1.
    split.
    -- apply (wf_extend _ _ _ H0 H1).
    -- exact H0.
  - destruct IHwf_sb1.
    destruct IHwf_sb2.
    auto.
  - destruct IHwf_sb.
    split ; auto.
    apply (wf_extend _ _ _ H3 H0).
  - destruct IHwf_sb.
    apply (presup_ctx_eq) in H0.
    destruct H0.
    auto.
Qed.

Lemma presup_tm_eq (Γ : Ctx) (s t : exp) (T : Typ) : Γ ⊢ s ≈ t : T -> (⊢ Γ ∧ Γ ⊢ s : T).
Proof.
  assert (presup_tm_eq : ∀ Γ s t T,  (Γ ⊢ s ≈ t : T) -> ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i, Γ ⊢ T : typ i) by admit.
  intros.
  induction H; try destruct (presup_sb _ _ _ H).
  - pose proof (wf_univ_nat_f _ i H0).
    pose proof (wf_univ_nat_f _ i H1).
    split ;auto.
    pose proof (wf_sub _ _ _ _ _ H H3).
    apply (wf_conv _ _ _ _ (i+1) H4).
    exact (wf_eq_typ_sub _ _ _ _ H).
    
  - split;auto.
    pose proof (wf_univ _ (i) H1).
    pose proof (wf_univ _ (i) H0).
    pose proof (wf_sub _ _ _ _ _ H H2).
    apply (wf_conv _ _ _ _ (i+1+1) H4).
    exact (wf_eq_typ_sub _ _ _ _ H).
    
  - split; auto.
    pose proof (wf_pi _ _ _ _ H0 H1).
    pose proof (wf_sub _ _ _ _ _ H H4).
    apply (wf_conv _ _ _ _ (i+1) H5).
    exact (wf_eq_typ_sub _ _ _ _ H).
  - split;auto.
    -- destruct IHwf_term_eq1.
       exact H2.
    -- apply (wf_pi).
       destruct IHwf_term_eq1.
       auto.
       destruct IHwf_term_eq2.
       auto.

  - split;auto.
    apply (wf_vlookup _ _ _ H H0).
  - split;try constructor;auto.

  - split;auto.
    pose proof (wf_zero _  H1).
    pose proof (wf_sub _ _ _ _ _ H H2).
    apply (wf_conv _ _ _ _ 1 H3).
    exact (wf_eq_nat_sub _ _ _ _ H).

  - destruct IHwf_term_eq.
    split;try constructor;auto.

  - split;auto.
    pose proof (wf_succ _ _ H0).
    pose proof (wf_sub _ _ _ _ _ H H3).
    apply (wf_conv _ _ _ _ 1 H4).
    exact (wf_eq_nat_sub _ _ _ _ H).

  - destruct IHwf_term_eq.
    split;auto.
    -- destruct (presup_sb_eq _ _ _ _ H0).
       auto.
    -- destruct (presup_sb_eq _ _ _ _ H0).
       destruct H4.
       destruct H5.
       exact (wf_sub _ _ _ _ _ H5 H2).
       
  - destruct (presup_tm _ _ _ H).
    split.
    -- auto.
    -- pose proof (wf_sb_id _ H0).
       destruct H1.
       pose proof (wf_sub _ _ _ _ _ H2 H).
       apply (wf_conv _ _ _ _ x H3).
       apply (wf_eq_sub_id _ _ _ H1).
  - split.
    -- auto.
    -- destruct (ctx_decomp _ _  H).
       pose proof (wf_sb_weaken _ _ H).
       pose proof (wf_vlookup _ _ _ H1 H0).
       exact (wf_sub _ _ _ _ _ H3 H4).
  
  - split;auto.
    eapply (wf_sub _ _ _ _ _ _ H1).

  - split;auto.
    pose proof (wf_sb_extend _ _ _ _ _ _ H H0 H1).
    pose proof (here T Δ).
    pose proof (wf_extend _ _ _ H3 H0).
    pose proof (wf_vlookup _ _ _ H6 H5).
    pose proof (wf_sub _ _ _ _ _ H4 H7).
    apply (wf_conv _ _ _ _ i H8).    
    pose proof (wf_sub_eq_p_ext _ _ _ _ _ _ H H0 H1).
    pose proof (tm_eq_refl _ _ _ H0).
    pose proof (wf_eq_sub_cong _ _ _ _ _ _ _ H10 H9).
    pose proof (wf_sb_weaken _ _ H6).
    pose proof (wf_eq_sub_comp _ _ _ _ _ _ _ H4 H12 H0).
    pose proof (wf_eq_trans _ _ _ _ _ (wf_eq_sym _ _ _ _ H13) H11).
    apply (wf_eq_conv _ _ _ _ _ (i+1) H14).
    pose proof (wf_sb_compose _ _ _ _ _ H4 H12).
    exact (wf_eq_typ_sub _ _ _ _ H15).
    
  - split;auto.
    pose proof (wf_extend _ _ _ H4 H0).
    pose proof (there _ _ _ T H2).
    pose proof (wf_sb_extend _ _ _ _ _ _ H H0 H1).
    pose proof (wf_vlookup _ _ _ H5 H6).
    pose proof (wf_sub _ _ _ _ _ H7 H8).
    apply (wf_conv _ _ _ _ i H9).
    pose proof (wf_sb_weaken _ _ H5).
    pose proof (wf_eq_sub_comp _ _ _ _ _ _ _ H7 H10 H0).
    pose proof (wf_sb_compose _ _ _ _ _ H7 H10).
    pose proof (wf_eq_typ_sub _ _ _ (i) H12).
    pose proof (wf_eq_conv _ _ _ _ _ (i+1) H11 H13).
    pose proof (wf_sub_eq_sym _ _ _ _ (wf_sub_eq_p_ext _ _ _ _ _ _ H H0 H1)).
    pose proof (wf_eq_sub_cong _ _ _ _ Γ σ (a_weaken ∙ (σ,, t)) (tm_eq_refl _ _ _ H0) H15).
    apply (wf_eq_trans _ _ _ _ _ (wf_eq_sym _ _ _ _ H14)).
    apply (wf_eq_conv _ _ _ _ _ (i+1) (wf_eq_sym _ _ _ _ H16)).
    exact (wf_eq_typ_sub _ _ _ _ H).

  - destruct IHwf_term_eq.
    split;auto.
    constructor;auto.

  - destruct IHwf_term_eq1.
    destruct IHwf_term_eq2.
    split;auto.
    exact (wf_conv _ _ _ _ _ H2 H0).

  - destruct IHwf_term_eq.
    split;auto.
    destruct (presup_tm_eq _ _ _ _ H) as [_ [_ [P _]]].
    exact P.
  - exact IHwf_term_eq1.
Admitted.  

Lemma presup_tm_eq' (Γ : Ctx) (s t : exp) (T : Typ) : Γ ⊢ s ≈ t : T -> (⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  induction H; try destruct (presup_sb _ _ _ H).
  - pose proof (wf_univ_nat_f _ i H0).
    pose proof (wf_univ_nat_f _ i H1).
    split ;auto.
    split.
    -- pose proof (wf_sub _ _ _ _ _ H H3).
       apply (wf_conv _ _ _ _ (i+1) H4).
       exact (wf_eq_typ_sub _ _ _ _ H).
    -- split;auto.
       exists (i+1).
       constructor.
       exact H0.

  - pose proof (wf_univ _ (i) H1).
    pose proof (wf_univ _ (i) H0).
    split;auto.
    pose proof (wf_sub _ _ _ _ _ H H2).
    split.
    -- apply (wf_conv _ _ _ _ (i+1+1) H4).
       exact (wf_eq_typ_sub _ _ _ _ H).
    -- split; auto.
       exists (i+ 1 + 1).
       constructor;auto.

  - pose proof (wf_pi _ _ _ _ H0 H1).
    pose proof (wf_sub _ _ _ _ _ H H4).
    split;auto.
    split.
    apply (wf_conv _ _ _ _ (i+1) H5).
    exact (wf_eq_typ_sub _ _ _ _ H).
    split.
    -- apply (wf_pi).
       pose proof (wf_sub _ _ _ _ _ H H0).
       apply (wf_conv _ _ _ _ (i+1) H6).
       exact (wf_eq_typ_sub _ _ _ _ H).  
       pose proof (presup_tm _ _ _ H1).
       (* Currently stuck *)
       admit.
    -- exists (i+1).
       constructor;auto.
  - destruct IHwf_term_eq1.
    destruct IHwf_term_eq2.
    split;auto.
    destruct H3.
    destruct H5.
    split.
    constructor;auto.
    destruct H6.
    destruct H7.
    split;try constructor;auto.
    (*Unfinished*)
  
Admitted.  
