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
  - split; mauto.
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

#[export]
Hint Resolve ctx_decomp presup_ctx_eq tm_eq_refl sb_eq_refl : mcltt.

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
  mauto.
Qed.  

#[export]
Hint Resolve sub_lvl sub_lvl_eq : mcltt.
 
(* Corresponds to ∈!⇒ty-wf in Agda proof *)
Lemma var_in_wf (Γ : Ctx) (T : Typ) (x : nat) : ⊢ Γ -> (x : T ∈! Γ) -> (∃ i, Γ ⊢ T : typ i).
Proof.
  intros.
  induction H0.
  - inversion H.
    mauto.
  - inversion H.
    destruct (IHctx_lookup H3).
    mauto.
Qed.

#[export]
Hint Resolve var_in_wf : mcltt.

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

#[export]
Hint Resolve presup_sb_ctx : mcltt.

Lemma presup_tm_ctx (Γ : Ctx) (t T : exp) : Γ ⊢ t : T -> ⊢ Γ.
Proof.
  intro.
  induction H;mauto.
  destruct (presup_sb_ctx _ _ _ H).
  mauto.
Qed.

#[export]
Hint Resolve presup_tm_ctx : mcltt.

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
    split;mauto.
    -- split;mauto.
  - intros.    
    inversion H.
    rewrite <- H7 in H.
    destruct (IHctx_lookup _ H3) as [X [i0 [nXD0 [GTX D0TX]]]].
    exists (a_sub X a_weaken).
    exists i0.
    split;mauto.
    -- split;mauto.
Qed.           

(* Corresponds to ⊢≈-sym in Agda proof *)
Lemma ctx_eq_sym (Γ Δ : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Δ ≈ Γ.
Proof.
  intros.
  induction H;mauto.
Qed.

#[export]
Hint Resolve var_in_eq ctx_eq_sym : mcltt. 

Lemma presup_sb_eq_ctx (Γ Δ : Ctx) (σ σ' : Sb) : Γ ⊢s σ ≈ σ' : Δ -> ⊢ Γ.
Proof.
  intros.
  induction H;try destruct (presup_sb_ctx _ _ _ H);mauto.
  Unshelve.
  exact 1.
Qed.

#[export]
Hint Resolve presup_sb_eq_ctx : mcltt. 

Lemma presup_tm_eq_ctx (Γ : Ctx) (t t' : exp) (T : Typ) : Γ ⊢ t ≈ t' : T -> ⊢ Γ.
Proof.
  intros.
  induction H;mauto.
  Unshelve.
  exact 0.
Qed.  

#[export]
Hint Resolve presup_tm_eq_ctx : mcltt.

