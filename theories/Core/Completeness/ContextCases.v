From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation System.
Import Domain_Notations.

Proposition valid_ctx_empty :
  {{ ⊨ ⋅ }}.
Proof.
  do 2 econstructor.
  apply Equivalence_Reflexive.
Qed.

Lemma rel_ctx_extend : forall {Γ Γ' A A' i},
    {{ ⊨ Γ ≈ Γ' }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ ⊨ Γ, A ≈ Γ', A' }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓΓ'] [env_relΓ].
  pose (env_relΓ0 := env_relΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  econstructor; eauto with typeclass_instances.
  - instantiate (1 := fun p p' (equiv_p_p' : env_relΓ p p') m m' =>
                        forall i a a' R,
                          {{ ⟦ A ⟧ p ↘ a }} ->
                          {{ ⟦ A' ⟧ p' ↘ a' }} ->
                          per_univ_elem i R a a' ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    destruct_by_head rel_typ.
    invert_rel_typ_body.
    destruct_by_head rel_exp.
    destruct_conjs.
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; handle_per_univ_elem_irrel...
  - apply Equivalence_Reflexive.
Qed.
