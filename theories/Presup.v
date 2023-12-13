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
    | [|- ?X ∧ ?Y] => split;splitting
    | [|- _] => mauto
    end
  in splitting
.

Ltac gen_presup_H :=
  let rec ctx_eq_helper :=
    match goal with
    | [H : ⊢ ?Γ ≈ ?Δ |- _] =>
        let HΓ := fresh "HΓ" in
        let HΔ := fresh "HΔ" in
        pose proof presup_ctx_eq _ _ H as [HΓ HΔ]; gen H; ctx_eq_helper; intro
    | _ => idtac
    end
  in
  let rec sb_helper :=
    match goal with
    | [H : ?Γ ⊢s ?σ : ?Δ |- _] =>
        let HΓ := fresh "HΓ" in
        let HΔ := fresh "HΔ" in
        pose proof presup_sb_ctx _ _ _ H as [HΓ HΔ]; gen H; sb_helper; intro
    | _ => idtac
    end
  in
  ctx_eq_helper; sb_helper.

Ltac gen_presup_IH presup_tm presup_eq presup_sb_eq :=
  let rec tm_helper :=
    match goal with
    | [H : ?Γ ⊢ ?t : a_typ ?i |- _] => gen H; tm_helper; intro
    | [H : ?Γ ⊢ ?t : ?T |- _] =>
        let HΓ := fresh "HΓ" in
        let i := fresh "i" in
        let HTi := fresh "HTi" in
        pose proof presup_tm _ _ _ H as [HΓ [i HTi]]; gen H; tm_helper; intro
    | _ => idtac
    end
  in
  let rec sb_eq_helper :=
    match goal with
    | [H : ?Γ ⊢s ?σ ≈ ?τ : ?Δ |- _] =>
        let HΓ := fresh "HΓ" in
        let Hσ := fresh "Hσ" in
        let Hτ := fresh "Hτ" in
        let HΔ := fresh "HΔ" in
        pose proof presup_sb_eq _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]; gen H; sb_eq_helper; intro
    | _ => idtac
    end
  in
  let rec eq_helper :=
    match goal with
    | [H : ?Γ ⊢ ?s ≈ ?t : ?T |- _] =>
        let HΓ := fresh "HΓ" in
        let i := fresh "i" in
        let Hs := fresh "Hs" in
        let Ht := fresh "Ht" in
        let HTi := fresh "HTi" in
        pose proof presup_eq _ _ _ _ H as [HΓ [Hs [Ht [i HTi]]]]; gen H; eq_helper; intro
    | _ => idtac
    end
  in
  tm_helper; sb_eq_helper; eq_helper.

Ltac gen_presup presup_tm presup_eq presup_sb_eq := gen_presup_IH presup_tm presup_eq presup_sb_eq; gen_presup_H.

Lemma presup_tm (Γ : Ctx) (t : exp) (T : Typ) (g_tm : Γ ⊢ t : T) :  ⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i
with presup_eq  (Γ : Ctx) (s t : exp) (T : Typ) (g_eq : Γ ⊢ s ≈ t : T) :  ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i,Γ ⊢ T : typ i
with presup_sb_eq (Γ Δ : Ctx) (σ τ : Sb) (g_seq : Γ ⊢s σ ≈ τ : Δ) : ⊢ Γ ∧ Γ ⊢s σ : Δ ∧ Γ ⊢s τ : Δ ∧ ⊢ Δ.                        
Proof with breakdown_goal.
  - inversion g_tm; clear g_tm; subst; gen_presup presup_tm presup_eq presup_sb_eq; breakdown_goal.
    -- exists i.
       eapply sub_lvl...
       econstructor...

    -- exists (max i i0).
       pose proof (lift_tm_max _ _ _ _ _ _ H HTi) as [Ga AGB].
       econstructor...
       
  - inversion g_eq; clear g_eq; subst; gen_presup presup_tm presup_eq presup_sb_eq; breakdown_goal.
    -- pose proof (wf_pi _ _ _ _ H0 H1)...
       econstructor...
       eapply (sub_lvl _ _ _ _ _ H1).
       econstructor...
       eapply wf_conv...
       eapply wf_eq_conv; mauto 6.

    -- econstructor; mauto using ctxeq_tm, ctx_eq_refl.

    -- econstructor...
       eapply wf_eq_conv; mauto using wf_eq_sub_cong.

    -- eapply wf_sub...
       econstructor...
       inversion H...

    -- eapply wf_conv; try now (econstructor; mauto).

    -- eapply wf_conv; try now (econstructor; mauto).
       eapply wf_eq_trans.
       + eapply wf_eq_sym.
         eapply wf_eq_conv.
         ++ eapply wf_eq_sub_comp...
         ++ do 2 (econstructor; mauto).
       + do 3 (econstructor; mauto).

    -- eapply wf_conv; try now (econstructor; mauto).
       eapply wf_eq_trans.
       + eapply wf_eq_sym.
         eapply wf_eq_conv.
         ++ eapply wf_eq_sub_comp...
         ++ do 2 (econstructor; mauto).
       + do 3 (econstructor; mauto).

  - inversion g_seq; clear g_seq; subst; gen_presup presup_tm presup_eq presup_sb_eq; breakdown_goal.
    -- inversion_clear H as [|D DTi]...

    -- econstructor...
       eapply wf_conv...

    -- econstructor...
       eapply wf_conv...
       eapply wf_eq_conv...

    -- inversion_clear HΔ as [|Γ0' T' i HΓ0 HT]...
       econstructor...
       eapply wf_conv...
       eapply wf_eq_conv...

    Unshelve.
    all: exact 0.
Qed.
