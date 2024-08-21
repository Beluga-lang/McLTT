From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_vlookup : forall {Γ x A},
    {{ ⊩ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊩ #x : A }}.
Proof.
  intros * [Sb] Hx. gen Sb.
  induction Hx; intros;
    match_by_head1 glu_ctx_env ltac:(fun H => dependent destruction H).
  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists.
    intros.
    destruct_by_head cons_glu_sub_pred.
    econstructor; mauto.
    enough {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@i }} as -> by eassumption.
    mauto 4.
  - assert {{ Γ ⊩ #n : A }} as Hn by mauto.
    assert {{ Γ ⊢ #n : A }} by mauto.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [j] by (gen_presups; mauto).
    destruct (invert_glu_rel_exp ltac:(eassumption) Hn) as [k].
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists (max j k).
    intros.
    destruct_by_head cons_glu_sub_pred.
    repeat match goal with
           | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
               match type of H with
               | __mark__ _ _ => fail 1
               | _ => edestruct H; [eassumption |]; mark H
               end
           end; unmark_all.
    simplify_evals.
    rename a into b.
    rename a0 into a.
    assert (exists Pmax Elmax, {{ DG a ∈ glu_univ_elem (max j k) ↘ Pmax ↘ Elmax }}) as [Pmax [Elmax]] by mauto using glu_univ_elem_cumu_max_right.
    econstructor; mauto.
    assert {{ ⊢ Γ, B }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@j }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@(max j k) }} as -> by mauto 3 using lift_exp_eq_max_left.
    assert {{ Γ ⊢ #n : A }} by mauto 4.
    assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 3.
    assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
    assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv; mauto 3).
    assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 3.
    eapply glu_univ_elem_exp_cumu_max_right; revgoals; mautosolve 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcltt.

Lemma glu_rel_exp_sub : forall {Γ σ Δ M A},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ M : A }} ->
    {{ Γ ⊩ M[σ] : A[σ] }}.
Proof.
  intros * Hσ HM.
  pose proof Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  destruct (invert_glu_rel_exp ltac:(eassumption) HM) as [i].
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert (exists i, {{ Δ ⊢ A : Type@i }}) as [j] by (gen_presups; firstorder).
  eexists; split; mauto.
  exists (max i j).
  intros.
  repeat match reverse goal with
         | H: context[glu_rel_sub_sub _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; [eassumption |]; mark H
             end
         | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; [eassumption |]; mark H
             end
         end; unmark_all.
  assert (exists Pmax Elmax, {{ DG a ∈ glu_univ_elem (max i j) ↘ Pmax ↘ Elmax }}) as [Pmax [Elmax]] by mauto using glu_univ_elem_cumu_max_left.
  econstructor; mauto.
  assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 3.
  assert {{ Δ0 ⊢ A[σ][σ0] ≈ A[σ∘σ0] : Type@(max i j) }} as -> by mauto 3 using lift_exp_eq_max_right.
  assert {{ Δ0 ⊢ M[σ][σ0] ≈ M[σ∘σ0] : A[σ∘σ0] }} as -> by mauto 3.
  eapply glu_univ_elem_exp_cumu_max_left; revgoals; mautosolve 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mcltt.
