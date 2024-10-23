From Coq Require Import Morphisms_Relations RelationClasses.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations.

Lemma rel_exp_of_typ_inversion1 : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} /\
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
          rel_exp A ρ A' ρ' (per_univ i).
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists;
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  eassumption.
Qed.

Lemma rel_exp_of_typ_inversion2 : forall {Γ env_rel A A' i},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp A ρ A' ρ' (per_univ i).
Proof.
  intros * ? []%rel_exp_of_typ_inversion1.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Ltac invert_rel_exp_of_typ H :=
  (unshelve epose proof (rel_exp_of_typ_inversion2 _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_inversion1 H) as []; clear H)
  + invert_rel_exp H.

Lemma rel_exp_of_typ : forall {Γ env_rel A A' i},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp A ρ A' ρ' (per_univ i)) ->
    {{ Γ ⊨ A ≈ A' : Type@i }}.
Proof.
  intros.
  eexists_rel_exp.
  intros.
  eexists; split; eauto.
  econstructor; mauto.
  per_univ_elem_econstructor; eauto.
  reflexivity.
Qed.

#[export]
Hint Resolve rel_exp_of_typ : mcltt.

Ltac eexists_rel_exp_of_typ :=
  unshelve eapply (rel_exp_of_typ _);
  shelve_unifiable;
  [eassumption |].

Lemma valid_exp_typ : forall {i Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ Type@i : Type@(S i) }}.
Proof.
  intros * [].
  eexists_rel_exp_of_typ.
  intros.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_exp_typ : mcltt.

Lemma rel_exp_typ_sub : forall {i Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ Type@i[σ] ≈ Type@i : Type@(S i) }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve rel_exp_typ_sub : mcltt.

Lemma rel_exp_cumu : forall {i Γ A A'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@(S i) }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1.
  destruct_conjs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  match_by_head per_univ_elem ltac:(fun H => apply per_univ_elem_cumu in H).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_cumu : mcltt.
