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
  match_by_head1 per_ctx_env ltac:(fun H => inversion H; subst; let n := numgoals in guard n <= 1).
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
  destruct_by_head rel_exp.
  match goal with
  | H : per_univ_elem _ _ d{{{ 𝕌@?i }}} d{{{ 𝕌@?i }}} |- _ =>
      invert_per_univ_elem H;
      apply_relation_equivalence;
      clear_refl_eqs
  end.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  exists (per_univ i).
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  unfold per_univ.
  eexists.
  per_univ_elem_econstructor; try (now eauto); try setoid_reflexivity.
  - eauto with typeclass_instances.
  - instantiate (1 := fun c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c') b b' => forall a a' R, {{ ⟦ B ⟧ p ↦ c ↘ a }} -> {{ ⟦ B' ⟧ p' ↦ c' ↘ a' }} -> per_univ_elem i R a a' -> R b b').
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
    setoid_replace (fun b b' : domain =>
                      forall (a0 a'0 : domain) (R : Relation_Definitions.relation domain),
                        {{ ⟦ B ⟧ p ↦ c ↘ a0 }} -> {{ ⟦ B' ⟧ p' ↦ c' ↘ a'0 }} -> per_univ_elem i R a0 a'0 -> R b b') with elem_rel.
    + subst elem_rel; eassumption.
    + subst elem_rel; split; intros; handle_per_univ_elem_irrel; intuition.
  - match goal with
    | |- ?X <~> ?Y => instantiate (1 := Y)
    end.
    reflexivity.
Qed.      
