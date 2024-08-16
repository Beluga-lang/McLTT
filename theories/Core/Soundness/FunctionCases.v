From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import ContextCases LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma sub_eq_p_q_sigma_compose_tau_extend : forall {Δ' τ Δ M A i σ Γ}, {{ Δ ⊢s σ : Γ }} -> {{ Δ' ⊢s τ : Δ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Δ' ⊢ M : A[σ][τ] }} -> {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ }} by mauto 4.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ] }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(τ,,M) ≈ τ : Δ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ (Wk∘q σ)∘(τ,,M) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ (σ∘Wk)∘(τ,,M) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘τ : Γ }} by mauto 4.
  mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcltt.

Lemma glu_rel_exp_pi : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Π A B : Type@i }}.
Proof.
  intros * HA HB.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  assert {{ Γ, A ⊨ B : Type@i }} as HBcomp by mauto using completeness_fundamental_exp.
  pose proof HA as [SbΓ].
  pose proof HB as [SbΓA].
  destruct_conjs.
  match_by_head glu_ctx_env progressive_invert. (* TODO: define a better inversion tactic for glu_ctx_env *)
  handle_functional_glu_ctx_env.
  rename i0 into j.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ cons_glu_sub_pred j Γ A TSb }} by (econstructor; try solve_refl; apply_predicate_equivalence; eassumption).
  destruct (invert_glu_rel_exp ltac:(eassumption) HB) as [k].
  eexists; split; mauto.
  eexists (S (max i j)).
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  repeat match goal with
         | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; [eassumption |]; mark H
             end
         end; unmark_all.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  rename m into a.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [in_rel] by mauto.
  assert {{ DG 𝕌@i ∈ glu_univ_elem (S (max i j)) ↘ univ_glu_typ_pred i (S (Nat.max i j)) ↘ univ_glu_exp_pred i (S (Nat.max i j)) }} by (glu_univ_elem_econstructor; lia + reflexivity).
  pose proof (rel_exp_of_typ_inversion HBcomp) as [env_relΓA].
  destruct_conjs.
  pose env_relΓA.
  match_by_head (per_ctx_env env_relΓA) invert_per_ctx_env.
  assert {{ Dom ρ ≈ ρ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  pose in_rel.
  destruct_rel_typ.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  assert (i < S (max i j)) by lia.
  simpl; repeat split; mauto 3.
  do 2 eexists.
  split.
  - glu_univ_elem_econstructor; mauto; try reflexivity.
    + instantiate (1 := fun c _ Γ A M m => forall b OPc OElc,
                            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                            {{ DG b ∈ glu_univ_elem i ↘ OPc ↘ OElc }} ->
                            {{ Γ ⊢ M : A ® m ∈ OElc }}).
      instantiate (1 := fun c _ Γ A => forall b OPc OElc,
                            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                            {{ DG b ∈ glu_univ_elem i ↘ OPc ↘ OElc }} ->
                            {{ Γ ⊢ A ® OPc }}).
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ ↦ c ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
      apply_relation_equivalence.
      (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
      functional_eval_rewrite_clear.
      assert (exists P El, {{ DG b ∈ glu_univ_elem i ↘ P ↘ El }}) as [Pb [Elb]] by mauto.
      eapply simple_glu_univ_elem_morphism_iff; try reflexivity; mauto 3;
        split; intros; intuition; handle_functional_glu_univ_elem; eassumption.
    + per_univ_elem_econstructor; mauto; try solve_refl.
      instantiate (1 := fun c c' _ m m' => forall b b' out_rel,
                            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                            {{ ⟦ B ⟧ ρ ↦ c' ↘ b' }} ->
                            {{ DF b ≈ b' ∈ per_univ_elem i ↘ out_rel }} ->
                            {{ Dom m ≈ m' ∈ out_rel }}).
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ ↦ c' ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
      apply_relation_equivalence.
      (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
      destruct_by_head per_univ.
      econstructor; mauto.
      rewrite <- per_univ_elem_morphism_iff; try reflexivity; mauto.
      split; intros; intuition; handle_per_univ_elem_irrel; eassumption.
  - econstructor; mauto 3; intros;
      assert {{ Δ0 ⊢s σ0 : Δ }} by mauto 2.
    + assert {{ Δ0 ⊢s σ ∘ σ0 ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
      assert (glu_rel_exp_sub H4 Δ0 A {{{ Type @ i }}} {{{ σ ∘ σ0 }}} ρ) as [] by mauto.
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      apply_predicate_equivalence.
      unfold univ_glu_exp_pred' in *.
      destruct_conjs.
      handle_functional_glu_univ_elem.
      enough {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Type@i }} as <-; mauto 3.
    + rename a0 into c.
      assert {{ Dom ρ ↦ c ≈ ρ ↦ c ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
      apply_relation_equivalence.
      (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
      destruct_by_head per_univ.
      functional_eval_rewrite_clear.
      assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
      assert {{ Δ0 ⊢ m : A[σ][σ0] }} by mauto 3 using glu_univ_elem_trm_escape.
      assert {{ Δ0 ⊢s σ0,,m : Δ, A[σ] }} by mauto 3.
      repeat match goal with
             | H: context[glu_rel_typ_sub _ _ _ _ _] |- _ =>
                 match type of H with
                 | __mark__ _ _ => fail 1
                 | _ => edestruct H; [rewrite_predicate_equivalence_left; eassumption |]; mark H
                 end
             end; unmark_all.
      functional_eval_rewrite_clear.
      assert (cons_glu_sub_pred j Γ A TSb Δ0 {{{ q σ∘(σ0,,m) }}} d{{{ ρ ↦ c }}}) as Hconspred.
      {
        assert {{ ⊢ Γ, A }} by mauto 3.
        assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
        assert {{ Δ0 ⊢s q σ ∘ (σ0,,m) : Γ, A }} by mauto 3.
        assert {{ Δ0 ⊢s Wk ∘ (q σ ∘ (σ0,,m)) : Γ }} by mauto 3.
        assert {{ Δ0 ⊢ m : A[σ∘σ0] }} by mauto 3.
        assert {{ Δ0 ⊢ m : A[σ][σ0] }} by mauto 3.
        assert {{ Δ0 ⊢s (σ∘σ0),,m : Γ, A }} by mauto 3.
        assert {{ Δ0 ⊢s q σ ∘ (σ0,,m) ≈ (σ∘σ0),,m : Γ, A }} by mauto 3 using sub_decompose_q.
        assert {{ Δ0 ⊢ #0[q σ ∘ (σ0,,m)] ≈ #0[(σ∘σ0),,m] : A[Wk][(q σ ∘ (σ0,,m))] }} by mauto 3.
        econstructor; mauto 3.
        - assert {{ Δ0 ⊢ #0[q σ ∘ (σ0,,m)] ≈ #0[(σ∘σ0),,m] : A[Wk∘(q σ ∘ (σ0,,m))] }} as -> by mauto 3.
          assert {{ Δ0 ⊢ #0[(σ∘σ0),,m] ≈ m : A[σ∘σ0] }} by mauto 3.
          assert {{ Δ0 ⊢s Wk∘(q σ ∘ (σ0,,m)) ≈ σ∘σ0 : Γ }} by mauto 3.
          assert {{ Δ0 ⊢ #0[(σ∘σ0),,m] ≈ m : A[Wk∘(q σ ∘ (σ0,,m))] }} as -> by mauto 4.
          assert {{ Δ0 ⊢ A[Wk∘(q σ ∘ (σ0,,m))] ≈ A[σ∘σ0] : Type@j }} as -> by mauto 3.
          assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Type@j }} as -> by mauto 3.
          eapply glu_univ_elem_exp_conv; revgoals; mauto.
          eapply glu_univ_elem_typ_monotone; mauto.
        - assert {{ EG Γ ∈ glu_ctx_env ↘ TSb }} by (apply_predicate_equivalence; eassumption).
          assert {{ Δ0 ⊢s Wk∘(q σ ∘ (σ0,,m)) ≈ σ∘σ0 : Γ }} as -> by mauto 3.
          eapply glu_ctx_env_sub_monotone; intuition.
      }
      (on_all_hyp: fun H => destruct (H _ _ _ Hconspred)).
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      apply_predicate_equivalence.
      unfold univ_glu_exp_pred' in *.
      destruct_conjs.
      handle_functional_glu_univ_elem.
      enough {{ Δ0 ⊢ B[q σ∘(σ0,,m)] ≈ B[q σ][σ0,,m] : Type@i }} as <- by eassumption.
      assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 4.
      assert {{ Δ0 ⊢ m : A[σ][σ0] }} by mauto 4 using glu_univ_elem_trm_escape.
      mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mcltt.

Lemma glu_rel_exp_fn : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_fn : mcltt.

Lemma glu_rel_exp_app : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_app : mcltt.
