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
    match_by_head1 glu_ctx_env ltac:(fun H => invert_glu_ctx_env H).
  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists.
    intros.
    destruct_by_head cons_glu_sub_pred.
    econstructor; mauto.
    enough {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@i }} as -> by eassumption.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊩ #n : A }} as Hn by mauto.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [j] by (gen_presups; mauto 3).
    invert_glu_rel_exp Hn.
    rename x into k.
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists (max j k).
    intros.
    destruct_by_head cons_glu_sub_pred.
    destruct_glu_rel_exp_sub.
    simplify_evals.
    rename a into b.
    rename a0 into a.
    assert {{ Dom a ≈ a ∈ per_univ k }} as [] by mauto.
    eapply mk_glu_rel_exp_sub''; gintuition mauto using per_univ_elem_cumu_max_right.
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
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  invert_glu_rel_exp HM.
  rename x into i.
  assert (exists i, {{ Δ ⊢ A : Type@i }}) as [j] by (gen_presups; firstorder).
  eexists; split; mauto.
  exists (max i j).
  intros.
  destruct_glu_rel_sub_sub.
  destruct_glu_rel_exp_sub.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [] by mauto.
  eapply mk_glu_rel_exp_sub''; mauto using per_univ_elem_cumu_max_left.
  intros.
  assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 3.
  assert {{ Δ0 ⊢ A[σ][σ0] ≈ A[σ∘σ0] : Type@(max i j) }} as -> by mauto 3 using lift_exp_eq_max_right.
  assert {{ Δ0 ⊢ M[σ][σ0] ≈ M[σ∘σ0] : A[σ∘σ0] }} as -> by mauto 3.
  eapply glu_univ_elem_exp_cumu_max_left; revgoals; mautosolve 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mcltt.
