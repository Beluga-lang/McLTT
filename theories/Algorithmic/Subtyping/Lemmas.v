From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System Evaluation Readback NbE CoreTypeInversions Presup CtxSub SystemOpt.
From Mcltt.Core.Completeness Require Import Consequences.Rules.
From Mcltt Require Import Completeness Soundness.
From Mcltt.Algorithmic Require Import Subtyping.Definitions.
Import Syntax_Notations.

#[local]
  Ltac apply_subtyping :=
  repeat match goal with
    | H : {{ ~?Γ ⊢ ~?A : ~?M }},
        H1 : {{ ~?Γ ⊢ ~?M ⊆ ~?N }} |- _ =>
        assert {{ Γ ⊢ A : N }} by mauto; clear H
    end.

Lemma alg_subtyping_nf_sound : forall M N,
    {{ ⊢anf M ⊆ N }} ->
    forall Γ i,
      {{ Γ ⊢ M : Type@i }} ->
      {{ Γ ⊢ N : Type@i }} ->
      {{ Γ ⊢ M ⊆ N }}.
Proof.
  induction 1; intros; subst; simpl in *.
  - econstructor. mauto.
  - assert (i < j \/ i = j) as H2 by lia.
    destruct H2; mauto 3.
  - on_all_hyp: fun H => (apply wf_pi_inversion in H; destruct H as [? ?]).
    destruct_all.
    gen_presups.
    repeat match goal with
           | H : {{ ~?Γ ⊢ ~?M ⊆ ~?N }}, H1: {{ ⊢ ~?Γ , ~_ }} |- _ =>
               pose proof (wf_subtyp_univ_weaken _ _ _ _ H H1);
               fail_if_dup
           end.
    apply_subtyping.
    deepexec IHalg_subtyping_nf ltac:(fun H => pose proof H).
    mauto 3.
Qed.

Lemma alg_subtyping_nf_trans : forall M1 M0 M2,
    {{ ⊢anf M0 ⊆ M1 }} ->
    {{ ⊢anf M1 ⊆ M2 }} ->
    {{ ⊢anf M0 ⊆ M2 }}.
Proof.
  intro M1; induction M1; intros ? ? H1 H2;
    dependent destruction H1;
    dependent destruction H2;
    simpl in *;
    try contradiction;
    mauto.
  apply asnf_univ. lia.
Qed.

Lemma alg_subtyping_nf_refl : forall M,
    {{ ⊢anf M ⊆ M }}.
Proof.
  intro M; induction M;
    solve [constructor; simpl; trivial].
Qed.

#[local]
 Hint Resolve alg_subtyping_nf_trans alg_subtyping_nf_refl : mcltt.

Lemma alg_subtyping_trans : forall Γ M0 M1 M2,
    {{ Γ ⊢a M0 ⊆ M1 }} ->
    {{ Γ ⊢a M1 ⊆ M2 }} ->
    {{ Γ ⊢a M0 ⊆ M2 }}.
Proof.
  intros. progressive_inversion.
  functional_nbe_rewrite_clear.
  mauto.
Qed.

#[local]
 Hint Resolve alg_subtyping_trans : mcltt.


Lemma alg_subtyping_complete : forall Γ M N,
    {{ Γ ⊢ M ⊆ N }} ->
    {{ Γ ⊢a M ⊆ N }}.
Proof.
  induction 1; mauto.
  - apply completeness in H.
    destruct H as [W [? ?]].
    econstructor; mauto.
  - assert {{ Γ ⊢ Type@i : Type@(S i) }} by mauto.
    assert {{ Γ ⊢ Type@j : Type@(S j) }} by mauto.
    on_all_hyp: fun H => apply soundness in H.
    destruct_all.
    econstructor; try eassumption.
    progressive_inversion.
    mauto.
  - assert {{ Γ ⊢ Π A B : Type@i }} as HΠ1 by mauto.
    assert {{ Γ ⊢ Π A' B' : Type@i }} as HΠ2 by mauto.
    assert {{ ⊢ Γ , A ≈ Γ , A' }} by mauto.
    eapply ctxeq_nbe_eq in H5; [ |eassumption].
    match goal with
    | H : _ |- _ => apply completeness in H
    end.
    apply soundness in HΠ1.
    apply soundness in HΠ2.
    destruct_all.
    econstructor; try eassumption.
    progressive_inversion.
    simpl in *.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear.
    eapply asnf_pi; trivial.
Qed.

Lemma alg_subtyping_sound : forall Γ M N i,
    {{ Γ ⊢a M ⊆ N }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢ N : Type@i }} ->
    {{ Γ ⊢ M ⊆ N }}.
Proof.
  intros. destruct H.
  on_all_hyp: fun H => apply soundness in H.
  destruct_all.
  functional_nbe_rewrite_clear.
  gen_presups.
  eapply alg_subtyping_nf_sound in H3; try eassumption.
  etransitivity; [mauto |].
  etransitivity; [eassumption |].
  mauto.
Qed.
