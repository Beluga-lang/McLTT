Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Export Mcltt.System.
Require Export Mcltt.LibTactics.

Lemma ctx_decomp (Γ : Ctx) (T : Typ) : ⊢ T :: Γ -> (⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  inversion H.
  split;mauto.
Qed.  

(* Corresponds to presup-⊢≈ in the Agda proof*)
Lemma presup_ctx_eq (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Γ ∧ ⊢ Δ.
Proof.
  intro.
  induction H.
  - split; exact wf_empty.
  - destruct IHwf_ctx_eq.
    split.
    inversion H3.
    1-2: rewrite H8; mauto.
    1-2: rewrite H10; mauto.
    rewrite H9; mauto.
    rewrite <- H9;rewrite H8;mauto.
    1-5: mauto.
Qed.

(* Corresponds to ≈-refl in the Agda code*)
Lemma tm_eq_refl (Γ : Ctx) (t: exp) (T : Typ) : Γ ⊢ t : T -> Γ ⊢ t ≈ t : T.
Proof.
  mauto.
Qed.
Lemma sb_eq_refl (Γ Δ : Ctx) (σ : Sb) : Γ ⊢s σ : Δ -> Γ ⊢s σ ≈ σ : Δ.
Proof.
  intros.
  mauto.
Qed.

(* Corresponds to t[σ]-Se in the Agda proof *)
Lemma sub_lvl (Δ Γ : Ctx) (T : Typ) (σ : Sb) (i : nat) : (Δ ⊢ T : typ i) -> (Γ ⊢s σ : Δ) -> (Γ ⊢ a_sub T σ : typ i).
Proof.
  intros.
  mauto.
Qed.  

(* Corresponds to []-cong-Se′ in the Agda proof*)
Lemma sub_lvl_eq (Δ Γ : Ctx) (T T': Typ) (σ : Sb) (i : nat) : (Δ ⊢ T ≈ T' : typ i) -> (Γ ⊢s σ : Δ) -> (Γ ⊢ a_sub T σ ≈ a_sub T' σ : typ i).
Proof.
  intros.
  mauto using sb_eq_refl.
Qed.  

(* Corresponds to ∈!⇒ty-wf in Agda proof *)
Lemma var_in_wf (Γ : Ctx) (T : Typ) (x : nat) : ⊢ Γ -> (x : T ∈! Γ) -> (∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  induction H0.
  - inversion H.
    mauto using sub_lvl.
  - inversion H.
    destruct (IHctx_lookup H3).
    mauto using sub_lvl.
Qed.

Lemma presup_sb_ctx (Γ Δ: Ctx) (σ : Sb) : Γ ⊢s σ : Δ -> ⊢ Γ ∧ ⊢ Δ.
Proof.
  intro.
  induction H;mauto.
  - destruct (ctx_decomp _ _ H).
    mauto.
  - destruct IHwf_sb1,IHwf_sb2.
    mauto.
  - destruct IHwf_sb.
    mauto.
  - destruct (presup_ctx_eq _ _ H0),IHwf_sb.
    mauto.
Qed.  

Lemma presup_tm_ctx (Γ : Ctx) (t T : exp) : Γ ⊢ t : T -> ⊢ Γ.
Proof.
  intro.
  induction H;mauto using presup_sb_ctx.
  destruct (presup_sb_ctx _ _ _ H).
  mauto.
Qed.

(* Corresponds to ∈!⇒ty≈ in Agda proof *)
Lemma var_in_eq (Γ Δ : Ctx) (T : Typ) (x : nat) :  ⊢ Γ ≈ Δ -> (x : T ∈! Γ) -> (∃ T' i, (x : T' ∈! Δ ∧ Γ ⊢ T ≈ T' : typ i ∧ Δ ⊢ T ≈T' : typ i)).
Proof.
  intros.
  generalize dependent Δ.
  induction H0.
  - intros.
    destruct (presup_ctx_eq _ _ H).
    destruct (ctx_decomp _ _ H0) as [G [x G_T]].
    inversion H.
    exists (a_sub T' a_weaken).    
    exists i.
    split.
    -- mauto using here.
    -- split.
       --- pose proof (wf_sb_weaken _ _ H0).
           mauto using (wf_eq_sub_cong, wf_sb_weaken,sb_eq_refl).
       --- rewrite <- H8 in H1, H.
           pose proof (wf_sb_weaken _ _ H1).
           mauto using (wf_eq_sub_cong,sb_eq_refl,wf_sb_weaken).
  - intros.    
    inversion H.
    rewrite <- H7 in H.
    destruct (IHctx_lookup _ H3) as [X [i0 [nXD0 [GTX D0TX]]]].
    exists (a_sub X a_weaken).
    exists i0.
    split.
    -- mauto using there.
    -- destruct (presup_ctx_eq _ _ H) as [T'G T0D0].
       pose proof (wf_sb_weaken _ _ T'G).
       pose proof (wf_sb_weaken _ _ T0D0).
       split.
       --- eapply wf_eq_conv.
           eapply wf_eq_sub_cong;mauto using sb_eq_refl.
           mauto.
       --- eapply wf_eq_conv.
           eapply wf_eq_sub_cong;mauto using sb_eq_refl.
           mauto.
Qed.           


(* Corresponds to ⊢≈-sym in Agda proof *)
Lemma ctx_eq_sym (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Δ ≈ Γ.
Proof.
  intros.
  induction H.
  - mauto.
  - eapply (wfc_extend _ _ _ _ _ IHwf_ctx_eq);mauto.
Qed.

