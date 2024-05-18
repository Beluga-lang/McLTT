From Coq Require Import Morphisms_Relations RelationClasses SetoidTactics.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation Completeness.TermStructureCases System.
Import Domain_Notations.

#[local]
Ltac extract_output_info_with p c p' c' env_rel :=
  let Hequiv := fresh "equiv" in
  (assert (Hequiv : {{ Dom p ↦ c ≈ p' ↦ c' ∈ env_rel }}) by (apply_relation_equivalence; eexists; eauto);
   apply_relation_equivalence;
   (on_all_hyp: fun H => destruct (H _ _ Hequiv) as [? []]);
   destruct_by_head rel_typ;
   destruct_by_head rel_exp).

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
  eexists ?[elem_rel].
  per_univ_elem_econstructor; try (now eauto); try setoid_reflexivity.
  - eauto with typeclass_instances.
  - instantiate (1 := fun c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c') b b' =>
                        forall a a' R,
                          {{ ⟦ B ⟧ p ↦ c ↘ a }} ->
                          {{ ⟦ B' ⟧ p' ↦ c' ↘ a' }} ->
                          per_univ_elem i R a a' -> R b b').
    intros.
    extract_output_info_with p c p' c' env_relΓA.
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
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; handle_per_univ_elem_irrel; intuition.
  - match goal with
    | |- ?[elem_rel] <~> ?Y => instantiate (elem_rel := Y)
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
  eexists ?[elem_rel].
  per_univ_elem_econstructor; eauto with typeclass_instances.
  - instantiate (1 := fun c c' (equiv_c_c' : head_rel o o' H9 c c') b b' =>
                        forall a a' R,
                          {{ ⟦ B ⟧ o ↦ c ↘ a }} ->
                          {{ ⟦ B[q σ] ⟧ p' ↦ c' ↘ a' }} ->
                          per_univ_elem i R a a' -> R b b').
    intros.
    extract_output_info_with o c o' c' env_relΔA.
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
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros; handle_per_univ_elem_irrel; intuition.
    enough {{ ⟦ B[q σ] ⟧ p' ↦ c' ↘ m' }} by intuition.
    repeat econstructor; eauto.
  - match goal with
    | |- ?[elem_rel] <~> ?Y => instantiate (elem_rel := Y)
    end.
    reflexivity.
Qed.

Lemma rel_exp_fn_cong : forall {i Γ A A' B M M'},
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A ⊨ M ≈ M' : B }} ->
  {{ Γ ⊨ λ A M ≈ λ A' M' : Π A B }}.
Proof with intuition.
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
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  eexists ?[elem_rel].
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  - per_univ_elem_econstructor; [eapply per_univ_elem_cumu_max_left | | |]; eauto with typeclass_instances.
    + instantiate (1 := fun c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c') b b' =>
                          forall a a' R,
                            {{ ⟦ B ⟧ p ↦ c ↘ a }} ->
                            {{ ⟦ B ⟧ p' ↦ c' ↘ a' }} ->
                            per_univ_elem H3 R a a' -> R b b').
      intros.
      extract_output_info_with p c p' c' env_relΓA.
      econstructor; eauto.
      eapply per_univ_elem_cumu_max_right.
      apply -> per_univ_elem_morphism_iff; eauto.
      split; intros; handle_per_univ_elem_irrel...
    + match goal with
      | |- ?[elem_rel] <~> ?Y => instantiate (elem_rel := Y)
      end.
      reflexivity.
  - intros ? **.
    extract_output_info_with p c p' c' env_relΓA.
    econstructor; only 1-2: repeat econstructor; eauto.
    intros.
    handle_per_univ_elem_irrel...
Qed.

Lemma rel_exp_fn_sub : forall {Γ σ Δ A M B},
  {{ Γ ⊨s σ : Δ }} ->
  {{ Δ , A ⊨ M : B }} ->
  {{ Γ ⊨ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΔA].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΔA0 := env_relΔA).
  inversion_by_head (per_ctx_env env_relΔA); subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists; [eassumption |].
  eexists.
  intros.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
  eexists ?[elem_rel].
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  - per_univ_elem_econstructor; [eapply per_univ_elem_cumu_max_left | | |]; eauto with typeclass_instances.
    + instantiate (1 := fun c c' (equiv_c_c' : head_rel o o' H8 c c') b b' =>
                          forall a a' R,
                            {{ ⟦ B ⟧ o ↦ c ↘ a }} ->
                            {{ ⟦ B ⟧ o' ↦ c' ↘ a' }} ->
                            per_univ_elem H3 R a a' -> R b b').
      intros.
      extract_output_info_with o c o' c' env_relΔA.
      econstructor; eauto.
      eapply per_univ_elem_cumu_max_right.
      apply -> per_univ_elem_morphism_iff; eauto.
      split; intros; handle_per_univ_elem_irrel...
    + match goal with
      | |- ?[elem_rel] <~> ?Y => instantiate (elem_rel := Y)
      end.
      reflexivity.
  - intros ? **.
    extract_output_info_with o c o' c' env_relΔA.
    econstructor; only 1-2: repeat econstructor; simpl; mauto.
    intros.
    handle_per_univ_elem_irrel...
Qed.
