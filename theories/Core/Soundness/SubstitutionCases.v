From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_sub_id : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩s Id : Γ }}.
Proof.
  intros * [Sb].
  do 2 eexists; repeat split; mauto.
  intros.
  econstructor; mauto.
  enough {{ Δ ⊢s σ ≈ Id∘σ : Γ }} as <-; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_id : mcltt.

Lemma glu_rel_sub_weaken : forall {Γ A},
    {{ ⊩ Γ, A }} ->
    {{ Γ, A ⊩s Wk : Γ }}.
Proof.
  intros * [SbΓA].
  match_by_head1 glu_ctx_env invert_per_ctx_env.
  handle_functional_glu_ctx_env.
  do 2 eexists; repeat split; mauto.
  intros.
  destruct_by_head cons_glu_sub_pred.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_weaken : mcltt.

Lemma glu_rel_sub_compose : forall {Γ1 σ2 Γ2 σ1 Γ3},
    {{ Γ1 ⊩s σ2 : Γ2 }} ->
    {{ Γ2 ⊩s σ1 : Γ3 }} ->
    {{ Γ1 ⊩s σ1 ∘ σ2 : Γ3 }}.
Proof.
  intros * Hσ2 Hσ1.
  pose proof Hσ2 as [SbΓ1 [SbΓ2]].
  destruct_conjs.
  destruct (invert_glu_rel_sub1 ltac:(eassumption) Hσ1) as [SbΓ3].
  destruct_conjs.
  do 2 eexists; repeat split; mauto.
  intros.
  repeat match reverse goal with
         | H: context[glu_rel_sub_sub _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; try eassumption; mark H
             end
         end; unmark_all.
  econstructor; mauto.
  assert {{ Γ2 ⊢s σ1 : Γ3 }} by mauto.
  assert {{ Γ1 ⊢s σ2 : Γ2 }} by mauto.
  enough {{ Δ ⊢s (σ1 ∘ σ2) ∘ σ ≈ σ1 ∘ (σ2 ∘ σ) : Γ3 }} as -> by eassumption.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_compose : mcltt.

Lemma glu_rel_sub_extend : forall {Γ σ Δ M A i},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A[σ] }} ->
    {{ Γ ⊩s (σ ,, M) : Δ , A }}.
Proof.
  intros * Hσ HA HM.
  pose proof Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  unshelve epose proof (invert_glu_rel_exp _ HA) as [j]; shelve_unifiable; [eassumption |].
  unshelve epose proof (invert_glu_rel_exp _ HM) as [k]; shelve_unifiable; [eassumption |].
  do 2 eexists; repeat split; mauto.
  - assert {{ Δ ⊢ A : Type@(max i k) }} by mauto 4 using lift_exp_max_left.
    econstructor; mauto 3; try reflexivity.
    intros.
    repeat match reverse goal with
           | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
               match type of H with
               | __mark__ _ _ => fail 1
               | _ => edestruct H; [eassumption |]; mark H
               end
           end; unmark_all.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    rename m into a.
    assert (exists P El, {{ DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El }}) as [? []] by mauto using glu_univ_elem_cumu_max_left.
    econstructor; mauto.
    eapply glu_univ_elem_typ_cumu_max_left; revgoals; mautosolve.
  - intros.
    repeat match reverse goal with
           | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
               match type of H with
               | __mark__ _ _ => fail 1
               | _ => edestruct H; [eassumption |]; mark H
               end
           | H: context[glu_rel_sub_sub _ _ _ _ _] |- _ =>
               match type of H with
               | __mark__ _ _ => fail 1
               | _ => edestruct H; [eassumption |]; mark H
               end
           end; unmark_all.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    rename m0 into a.
    assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
    assert {{ Δ ⊢ A : Type@i }} by mauto 3.
    assert {{ Γ ⊢s σ : Δ }} by mauto 3.
    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4.
    assert (exists P El, {{ DG a ∈ glu_univ_elem (max i k) ↘ P ↘ El }}) as [Pmax [Elmax]] by mauto 3 using glu_univ_elem_cumu_max_left.
    econstructor; mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 3.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + assert {{ Δ, A ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)] : Type@i }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] : Type@i }} by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Type@i }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ][σ0] : Type@(max i k) }} as -> by mauto 3 using lift_exp_eq_max_left.
      assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 3).
      eapply glu_univ_elem_exp_cumu_max_right; revgoals; mautosolve.
    + enough {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} as ->; eassumption.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend : mcltt.
