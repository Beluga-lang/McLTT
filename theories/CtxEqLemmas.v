Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
(* Corresponds to presup-⊢≈ in the Agda proof*)
Lemma presup_ctx_eq (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Γ ∧ ⊢ Δ.
Proof.
  intro.
  induction H.
  split; exact wf_empty.
  destruct IHwf_ctx_eq.
  split.
  -apply (wf_extend _ _ _ H5 H0).
  -apply (wf_extend _ _ _ H6 H1).   
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
Lemma var_in_eq (Γ Δ : Ctx) (T : Typ) (x : nat) : ⊢ Γ ≈ Δ -> (x : T ∈! Γ) -> (∃ T' i, (x : T' ∈! Γ ∧ Γ ⊢ T ≈ T' : typ i ∧ Δ ⊢ T ≈T' : typ i)).
Proof.
  intros.
  pose proof (presup_ctx_eq _ _ H).
  destruct H1.
  induction H0.
  exists (a_sub T a_weaken).
  (* I think I can get this proof to go through, maybe with more lemmas, but I haven't figured it out yet *)
Admitted.

Lemma tm_eq_conv (Γ : Ctx) (T : Typ) (t t' : exp) : Γ ⊢ t : T -> Γ ⊢ t ≈ t' : T -> Γ ⊢ t' : T.
Proof.
  intros.
  induction H.
  (* Unfinished, but this really seems true so hopefully it goes through fine *)
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
  apply (tm_eq_conv Δ (typ i) T' T H1).
  exact (wf_eq_sym _ _ _ _ H4).
  exact (wf_eq_sym _ _ _ _ H4).
  exact (wf_eq_sym _ _ _ _ H3).
Qed.
