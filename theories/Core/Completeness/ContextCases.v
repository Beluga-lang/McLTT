From Coq Require Import Morphisms_Relations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation Completeness.LogicalRelation Completeness.UniverseCases.
Import Domain_Notations.

Proposition valid_ctx_empty :
  {{ ⊨ ⋅ }}.
Proof.
  do 2 econstructor.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_ctx_empty : mcltt.

Lemma rel_ctx_extend : forall {Γ Γ' A A' i},
    {{ ⊨ Γ ≈ Γ' }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ ⊨ Γ, A ≈ Γ', A' }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓΓ'] [env_relΓ]%rel_exp_of_typ_inversion.
  pose env_relΓ.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun p p' (equiv_p_p' : env_relΓ p p') m m' =>
                        forall i R,
                          rel_typ i A p A' p' R ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    destruct_by_head per_univ.
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; destruct_by_head rel_typ; handle_per_univ_elem_irrel...
    eapply H7.
    mauto.
  - apply Equivalence_Reflexive.
Qed.

Lemma rel_ctx_extend' : forall {Γ A i},
    {{ Γ ⊨ A : Type@i }} ->
    {{ ⊨ Γ, A }}.
Proof.
  intros.
  eapply rel_ctx_extend; eauto.
  destruct H as [? []].
  eexists. eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend rel_ctx_extend' : mcltt.


Lemma wf_ctx_sub_empty' :
  {{ SubE ⋅ <: ⋅ }}.
Proof. mauto. Qed.


Lemma wf_ctx_sub_extend' : forall Γ Δ i A A',
  {{ SubE Γ <: Δ }} ->
  {{ Γ ⊨ A : Type@i }} ->
  {{ Δ ⊨ A' : Type@i }} ->
  {{ Γ ⊨ A ⊆ A' }} ->
  {{ SubE Γ , A <: Δ , A' }}.
Proof.
  intros * H H1 H2 H3.
  pose proof H3.
  destruct H3 as [? [? []]].
  on_all_hyp: fun H => (eapply rel_ctx_extend' in H; destruct H).
  econstructor; mauto; intros.
  deepexec H3 ltac:(fun H => destruct H as [? [? [? [? []]]]]).
  simplify_evals. eassumption.
Qed.


#[export]
Hint Resolve wf_ctx_sub_empty' wf_ctx_sub_extend' : mcltt.
