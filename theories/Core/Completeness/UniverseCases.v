From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation.
Import Domain_Notations.

Lemma valid_exp_typ : forall {i Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ Type@i : Type@(S i) }}.
Proof.
  intros * [].
  eexists_rel_exp.
  intros.
  eexists (per_univ _).
  split; [> econstructor; only 1-2: econstructor; eauto ..]; [| eexists (per_univ _)];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

Lemma rel_exp_typ_sub : forall {i Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ Type@i[σ] ≈ Type@i : Type@(S i) }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  eexists (per_univ _).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..]; [| eexists (per_univ _)];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

Lemma rel_exp_cumu : forall {i Γ A A'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@(S i) }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  exists (per_univ (S i)).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  inversion_by_head rel_typ.
  inversion_by_head rel_exp.
  invert_rel_typ_body.
  destruct_conjs.
  match_by_head per_univ_elem ltac:(fun H => apply per_univ_elem_cumu in H).
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto; [| eexists; eauto].
  per_univ_elem_econstructor; eauto.
  reflexivity.
Qed.
