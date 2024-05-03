From Mcltt Require Import Base LibTactics Syntax System SystemLemmas.

#[local]
Ltac gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper H :=
  match type of H with
  | {{ ~?Γ ⊢ ~?M : ~?A }} => pose proof ctxeq_exp_helper _ _ _ H
  | {{ ~?Γ ⊢ ~?M ≈ ~?N : ~?A }} => pose proof ctxeq_exp_eq_helper _ _ _ _ H
  | {{ ~?Γ ⊢s ~?σ : ~?Δ }} => pose proof ctxeq_sub_helper _ _ _ H
  | {{ ~?Γ ⊢s ~?σ ≈ ~?τ : ~?Δ }} => pose proof ctxeq_sub_eq_helper _ _ _ _ H
  | _ => idtac
  end.

Lemma ctxeq_exp_helper : forall {Γ M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M : A }}
with
ctxeq_exp_eq_helper : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M ≈ M' : A }}
with
ctxeq_sub_helper : forall {Γ Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ : Γ' }}
with
ctxeq_sub_eq_helper : forall {Γ Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof with solve [mauto].
  (* ctxeq_exp_helper *)
  - intros * HM * HΓΔ. gen Δ.
    inversion_clear HM;
      (on_all_hyp: gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper);
      clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
      intros; destruct (presup_ctx_eq HΓΔ); mauto.
    all: try (rename B into C); try (rename A0 into B).
    2-4: assert {{ Δ ⊢ B : Type@i }} as HB by eauto.
    2-4: assert {{ ⊢ Γ, B ≈ Δ, B }} by mauto; clear HB.
    2-3: solve [mauto].

    + assert {{ ⊢ Γ, ℕ ≈ Δ, ℕ }} by (econstructor; mauto).
      assert {{ Δ, ℕ ⊢ B : Type@i }} by mauto.
      econstructor...

    + econstructor...

    + assert (exists B i, {{ #x : B ∈ Δ }} /\ {{ Γ ⊢ A ≈ B : Type@i }} /\ {{ Δ ⊢ A ≈ B : Type@i }}) as [? [? [? [? ?]]]]...

  (* ctxeq_exp_eq_helper *)
  - intros * HMM' * HΓΔ. gen Δ.
    inversion_clear HMM';
      (on_all_hyp: gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper);
      clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
      intros; destruct (presup_ctx_eq HΓΔ); mauto.
    all: try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    1-3: assert {{ ⊢ Γ, ℕ ≈ Δ, ℕ }} by (econstructor; mauto).
    1-3: assert {{ Δ, ℕ ⊢ B : Type@i }} by eauto.
    1-3: econstructor...
    1-5: assert {{ Δ ⊢ B : Type@i }} by eauto.
    1-5: assert {{ ⊢ Γ, B ≈ Δ, B }}...

    + assert (exists B i, {{ #x : B ∈ Δ }} /\ {{ Γ ⊢ A ≈ B : Type@i }} /\ {{ Δ ⊢ A ≈ B : Type@i }}) as [? [? [? [? ?]]]]...

    + inversion_clear HΓΔ as [|? Δ0 ? ? C'].
      assert (exists D i', {{ #x : D ∈ Δ0 }} /\ {{ Γ0 ⊢ B ≈ D : Type@i' }} /\ {{ Δ0 ⊢ B ≈ D : Type@i' }}) as [D [i0 [? [? ?]]]] by mauto.
      assert {{ Δ0, C' ⊢ B[Wk] ≈ D[Wk] : Type @ i0 }}...

  (* ctxeq_sub_helper *)
  - intros * Hσ * HΓΔ. gen Δ.
    inversion_clear Hσ;
      (on_all_hyp: gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper);
      clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
      intros; destruct (presup_ctx_eq HΓΔ); mauto.
    inversion_clear HΓΔ.
    econstructor...

  (* ctxeq_sub_eq_helper *)
  - intros * Hσσ' * HΓΔ. gen Δ.
    inversion_clear Hσσ';
      (on_all_hyp: gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper);
      clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
      intros; destruct (presup_ctx_eq HΓΔ); mauto.
    inversion_clear HΓΔ.
    eapply wf_sub_eq_conv...

  Unshelve.
  all: constructor.
Qed.

Lemma ctxeq_exp : forall {Γ Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof.
  eauto using ctxeq_exp_helper.
Qed.

Lemma ctxeq_exp_eq : forall {Γ Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof.
  eauto using ctxeq_exp_eq_helper.
Qed.

Lemma ctxeq_sub : forall {Γ Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof.
  eauto using ctxeq_sub_helper.
Qed.

Lemma ctxeq_sub_eq : forall {Γ Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof.
  eauto using ctxeq_sub_eq_helper.
Qed.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq : mcltt.
