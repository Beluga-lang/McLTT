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
    | [|- ?X ∧ ?Y] => split; splitting
    | [|- _] => mauto
    end
  in splitting
.

Ltac gen_presup_ctx H :=
  match type of H with
  | ⊢ ?Γ ≈ ?Δ =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_ctx_eq H as [HΓ HΔ]
  | ?Γ ⊢s ?σ : ?Δ =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sb_ctx H as [HΓ HΔ]
  | _ => idtac
  end.

Ltac gen_presup_IH presup_tm presup_eq presup_sb_eq H :=
  match type of H with
  | (?Γ ⊢ ?t : ?T) =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HTi := fresh "HTi" in
      pose proof presup_tm _ _ _ H as [HΓ [i HTi]]
  | ?Γ ⊢s ?σ ≈ ?τ : ?Δ =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sb_eq _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | ?Γ ⊢ ?s ≈ ?t : ?T =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let Hs := fresh "Hs" in
      let Ht := fresh "Ht" in
      let HTi := fresh "HTi" in
      pose proof presup_eq _ _ _ _ H as [HΓ [Hs [Ht [i HTi]]]]
  | _ => gen_presup_ctx H
  end.

Lemma presup_tm : forall {Γ t T}, Γ ⊢ t : T -> ⊢ Γ ∧ ∃ i, Γ ⊢ T : typ i
with presup_eq : forall {Γ s t T}, Γ ⊢ s ≈ t : T -> ⊢ Γ ∧ Γ ⊢ s : T ∧ Γ ⊢ t : T ∧ ∃ i,Γ ⊢ T : typ i
with presup_sb_eq : forall {Γ Δ σ τ}, Γ ⊢s σ ≈ τ : Δ -> ⊢ Γ ∧ Γ ⊢s σ : Δ ∧ Γ ⊢s τ : Δ ∧ ⊢ Δ.
Proof with mauto.
  - intros * Ht.
    inversion_clear Ht; (on_all_hyp: gen_presup_IH presup_tm presup_eq presup_sb_eq); breakdown_goal.
    -- eexists.
       eapply sub_lvl...
       econstructor...
    -- eexists.
       pose proof (lift_tm_max_left i0 H).
       pose proof (lift_tm_max_right i HTi).
       econstructor...

  - intros * Hst.
    inversion_clear Hst; (on_all_hyp: gen_presup_IH presup_tm presup_eq presup_sb_eq); breakdown_goal.
    -- econstructor...
       eapply sub_lvl...
       econstructor...
       eapply wf_conv...
       eapply wf_eq_conv; mauto 6.

    -- econstructor...
       eapply wf_eq_conv...

    -- eapply wf_sub...
       econstructor...
       inversion H...

    -- eapply wf_conv; [|eapply wf_eq_conv]...

    -- eapply wf_conv; [econstructor; mauto|].
       eapply wf_eq_trans.
       + eapply wf_eq_sym.
         eapply wf_eq_conv.
         ++ eapply wf_eq_sub_comp...
         ++ econstructor...
       + do 2 econstructor...

    -- eapply wf_conv; [econstructor; mauto|].
       eapply wf_eq_trans.
       + eapply wf_eq_sym.
         eapply wf_eq_conv.
         ++ eapply wf_eq_sub_comp...
         ++ econstructor...
       + do 2 econstructor...

  - intros * Hστ.
    inversion_clear Hστ; (on_all_hyp: gen_presup_IH presup_tm presup_eq presup_sb_eq); breakdown_goal.
    -- inversion_clear H...

    -- econstructor...
       eapply wf_conv...

    -- econstructor...
       eapply wf_conv...
       eapply wf_eq_conv...

    -- inversion_clear HΔ...
       econstructor...
       eapply wf_conv...
       eapply wf_eq_conv...

  Unshelve.
  all: exact 0.
Qed.

#[export]
Hint Resolve presup_tm presup_eq presup_sb_eq : mcltt.

Ltac gen_presup H := gen_presup_IH presup_tm presup_eq presup_sb_eq H; gen_presup_ctx H.
