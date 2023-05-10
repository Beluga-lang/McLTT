Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.PresupLemmas.
Require Export Lia.

(* Corresponds to t[σ]-Se in the Agda proof *)
Lemma sub_lvl (Δ Γ : Ctx) (T : Typ) (σ : Sb) (i : nat) : (Δ ⊢ T : typ i) -> (Γ ⊢s σ : Δ) -> (Γ ⊢ a_sub T σ : typ i).
Proof.
  intros.
  pose proof (wf_sub _ _ _ _ _ H0 H).
  apply (wf_conv _ _ _ _ (i+1) H1).
  exact (wf_eq_typ_sub _ _ _ _ H0).
Qed.  

(* Corresponds to []-cong-Se′ in the Agda proof*)
Lemma sub_lvl_eq (Δ Γ : Ctx) (T T': Typ) (σ : Sb) (i : nat) : (Δ ⊢ T ≈ T' : typ i) -> (Γ ⊢s σ : Δ) -> (Γ ⊢ a_sub T σ ≈ a_sub T' σ : typ i).
Proof.
  intros.
  pose proof (wf_eq_typ_sub _ _ _ i H0).
  pose proof (sb_eq_refl _ _ _ H0).
  pose proof (wf_eq_sub_cong _ _ _ _ _ _ _ H H2).
  apply (wf_eq_conv _ _ _ _ _ _ H3 H1).
Qed.  



(* Corresponds to ∈!⇒ty-wf in Agda proof *)
Lemma var_in_wf (Γ : Ctx) (T : Typ) (x : nat) : ⊢ Γ -> (x : T ∈! Γ) -> (∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  induction H0.
  pose proof (ctx_decomp _ _ H).
  destruct H0.
  destruct H1.
  exists x.
  apply (sub_lvl Γ (T :: Γ) _ a_weaken x H1).
  apply (wf_sb_weaken _ _ H).
  pose proof (ctx_decomp _ _ H).
  destruct H1.
  destruct H2.
  pose proof (IHctx_lookup H1).
  destruct H3.
  exists x0.
  apply (sub_lvl Γ (T' :: Γ) _ a_weaken x0 H3).
  apply (wf_sb_weaken _ _ H).
Qed.


(* Corresponds to ∈!⇒ty≈ in Agda proof *)
Lemma var_in_eq  (Γ Δ : Ctx) (T : Typ) (x : nat) : ⊢ Γ ≈ Δ -> (x : T ∈! Γ) -> (∃ T' i, (x : T' ∈! Γ ∧ Γ ⊢ T ≈ T' : typ i ∧ Δ ⊢ T ≈T' : typ i)).
Proof.
  intros.
  pose proof (presup_ctx_eq _ _ H).
  destruct H1.
  induction H0.
  exists (a_sub T a_weaken).
  pose proof (wf_sb_weaken _ _ H1).
  destruct (ctx_decomp _ _ H1).
  destruct H4.
  pose proof (wf_sub _ _ _ _ _ H0 H4).
  exists (x).
  split.
  - exact (here _ _).
  - split.
    -- pose proof (tm_eq_refl _ _ _ H5).
       apply (wf_eq_conv _ _ _ _ _ (x+1) H6).
       exact (wf_eq_typ_sub _ _ _ _ H0).
    -- destruct H.
       --- pose proof (tm_eq_refl _ _ _ H5).
           apply (wf_eq_conv _ _ _ _ _ (x+1) H).
           exact (wf_eq_typ_sub _ _ _ _ H0).
       --- pose proof (wf_extend _ _ _ H3 H4).
           pose proof (wf_sb_weaken _ _ H11).
           admit.         
Admitted.


(* Corresponds to ⊢≈-sym in Agda proof *)
Lemma ctx_eq_sym (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Δ ≈ Γ.
Proof.
  intros.
  induction H.
  exact wfc_empty.
  apply (wfc_extend _ _ _ i _ IHwf_ctx_eq).
  exact H1.
  exact H0.
  destruct (presup_tm_eq _ _ _ _ H4).
  auto.
  exact (wf_eq_sym _ _ _ _ H4).
  exact (wf_eq_sym _ _ _ _ H3).
Qed.
