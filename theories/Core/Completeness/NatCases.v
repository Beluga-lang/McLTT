From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation System.
Import Domain_Notations.

Lemma valid_exp_nat : forall {Γ i},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ ℕ : Type@i }}.
Proof.
  intros * [env_relΓ].
  eexists_rel_exp.
  intros.
  eexists (per_univ _).
  split; [> econstructor; only 1-2: repeat econstructor ..]; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

Lemma rel_exp_nat_sub : forall {Γ σ i Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ ℕ[σ] ≈ ℕ : Type@i }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  eexists (per_univ _).
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto; [| eexists];
    per_univ_elem_econstructor; eauto; apply Equivalence_Reflexive.
Qed.

Lemma valid_exp_zero : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ zero : ℕ }}.
Proof.
  intros * [env_relΓ].
  unshelve eexists_rel_exp; [constructor |].
  intros.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor ..].
  - per_univ_elem_econstructor; reflexivity.
  - econstructor.
Qed.

Lemma rel_exp_zero_sub : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ zero[σ] ≈ zero : ℕ }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor.
Qed.

Lemma rel_exp_succ_sub : forall {Γ σ Δ M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ M : ℕ }} ->
    {{ Γ ⊨ (succ M)[σ] ≈ succ (M[σ]) : ℕ }}.
Proof.
  intros * [env_relΓ] [env_relΔ].
  destruct_conjs.
  pose (env_relΔ0 := env_relΔ).
  handle_per_ctx_env_irrel.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor; eassumption.
Qed.

Lemma rel_exp_succ_cong : forall {Γ M M'},
    {{ Γ ⊨ M ≈ M' : ℕ }} ->
    {{ Γ ⊨ succ M ≈ succ M' : ℕ }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  unshelve eexists_rel_exp; [constructor |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor ..]; eauto.
  - per_univ_elem_econstructor; reflexivity.
  - econstructor; eassumption.
Qed.
