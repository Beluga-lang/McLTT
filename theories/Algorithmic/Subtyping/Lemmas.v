From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System NbE CoreTypeInversions Presup CtxSub.
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
  - assert (i < j \/ i = j) by lia.
    destruct H2.
    + apply wf_subtyp_univ; mauto.
    + subst. mauto.
  - on_all_hyp: fun H => (apply wf_pi_inversion in H; destruct H as [? ?]).
    destruct_all.
    gen_presups.
    repeat match goal with
           | H : {{ ~?Γ ⊢ ~?M ⊆ ~?N }}, H1: {{ ⊢ ~?Γ , ~_ }} |- _ =>
               pose proof (wf_subtyp_univ_weaken _ _ _ _ H H1);
               fail_if_dup
           end.
    apply_subtyping.
    deepexec IHalg_subtyping_nf1 ltac:(fun H => pose proof H).
    eapply wf_subtyp_pi with (i := i); mauto 2.
    eapply IHalg_subtyping_nf2; try eassumption.
    mauto.
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
