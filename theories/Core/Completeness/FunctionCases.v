From Coq Require Import Morphisms_Relations RelationClasses SetoidTactics.
From Mcltt Require Import Base LibTactics LogicalRelation System.
Import Domain_Notations.

Lemma rel_exp_pi_cong : forall {i Γ A A' B B'},
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A ⊨ B ≈ B' : Type@i }} ->
  {{ Γ ⊨ Π A B ≈ Π A' B' : Type@i }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓA].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΓA0 := env_relΓA).
  inversion_by_head (per_ctx_env env_relΓA); subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists; [eassumption |].
  eexists.
  intros.
  (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
  rewrite_relation_equivalence_right.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  exists (per_univ i).
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  unfold per_univ.
  eexists.
  per_univ_elem_econstructor; try (now eauto); try setoid_reflexivity.
  - eauto with typeclass_instances.
  - instantiate (1 := fun c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c') b b' =>
                        forall a a' R,
                          {{ ⟦ B ⟧ p ↦ c ↘ a }} ->
                          {{ ⟦ B' ⟧ p' ↦ c' ↘ a' }} ->
                          per_univ_elem i R a a' -> R b b').
    intros.
    assert (equiv_pc_p'c' : {{ Dom p ↦ c ≈ p' ↦ c' ∈ env_relΓA }}) by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ equiv_pc_p'c') as [? []]).
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    inversion_by_head (eval_exp {{{ Type@i }}}).
    subst.
    match goal with
    | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
        invert_per_univ_elem H;
        apply_relation_equivalence;
        clear_refl_eqs
    end.
    destruct_conjs.
    econstructor; mauto.
    evar (elem_rel : relation domain).
    match goal with
    | |- per_univ_elem _ ?R _ _ => setoid_replace R with elem_rel; subst elem_rel; [eassumption |]
    end.
    split; intros; handle_per_univ_elem_irrel; intuition.
  - match goal with
    | |- ?X <~> ?Y => instantiate (1 := Y)
    end.
    reflexivity.
Qed.      

Lemma rel_exp_pi_sub : forall {i Γ σ Δ A B},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ , A ⊨ B : Type@i }} ->
    {{ Γ ⊨ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@i }}.
Proof.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [] [env_relΔA].
  destruct_conjs.
  pose (env_relΔA0 := env_relΔA).
  inversion_by_head (per_ctx_env env_relΔA); subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists; [eassumption |].
  eexists.
  intros.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split;
    [> econstructor; only 1-2: repeat econstructor; eauto ..].
  eexists.
  per_univ_elem_econstructor; eauto with typeclass_instances.
  - instantiate (1 := fun c c' (equiv_c_c' : head_rel o o' H9 c c') b b' =>
                        forall a a' R,
                          {{ ⟦ B ⟧ o ↦ c ↘ a }} ->
                          {{ ⟦ B[q σ] ⟧ p' ↦ c' ↘ a' }} ->
                          per_univ_elem i R a a' -> R b b').
    intros.
    assert (equiv_pc_p'c' : {{ Dom o ↦ c ≈ o' ↦ c' ∈ env_relΔA }}) by (apply_relation_equivalence; eexists; eauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ equiv_pc_p'c') as [? []]).
    destruct_by_head rel_typ.
    inversion_by_head (eval_exp {{{ Type@i }}}); subst.
    match goal with
    | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
        invert_per_univ_elem H;
        apply_relation_equivalence;
        clear_refl_eqs
    end.
    destruct_by_head rel_exp.
    destruct_conjs.
    econstructor; only 1-2: repeat econstructor; eauto.
    evar (elem_rel : relation domain).
    match goal with
    | |- per_univ_elem _ ?R _ _ => setoid_replace R with elem_rel; subst elem_rel; [eassumption |]
    end.
    split; intros; handle_per_univ_elem_irrel; intuition.
    enough {{ ⟦ B[q σ] ⟧ p' ↦ c' ↘ m' }} by intuition.
    repeat econstructor; eauto.
  - match goal with
    | |- ?X <~> ?Y => instantiate (1 := Y)
    end.
    reflexivity.
Qed.
