From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import ContextCases LogicalRelation SubstitutionCases SubtypingCases TermStructureCases UniverseCases.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma cons_glu_sub_pred_pi_helper : forall {Γ Sb Γ' σ ρ A a i P El Γ'' τ M c},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ'' ⊢w τ : Γ' }} ->
    {{ Γ'' ⊢ M : A[σ][τ] ® c ∈ El }} ->
    {{ Γ'' ⊢s σ∘τ,,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb }}.
Proof.
  intros.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ'' ⊢s τ : Γ' }} by mauto 2.
  assert {{ Γ'' ⊢ M : A[σ][τ] }} by mauto 2 using glu_univ_elem_trm_escape.
  assert {{ Γ'' ⊢ M : A[σ∘τ] }} by mauto 3.
  econstructor; mauto 3;
    assert {{ Γ'' ⊢s Wk∘(σ∘τ,,M) ≈ σ∘τ : Γ }} as -> by mauto 3.
  - assert {{ Γ'' ⊢ #0[σ∘τ,,M] ≈ M : A[σ∘τ] }} as -> by mauto 3.
    assert {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] : Type@i }} as -> by mauto 3.
    eassumption.
  - eapply glu_ctx_env_sub_monotone; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_pi_helper : mcltt.

Lemma glu_rel_exp_pi : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Π A B : Type@i }}.
Proof.
  intros * HA HB.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  assert {{ Γ ⊩ Type@i : Type@(S i) }} by mauto.
  invert_glu_rel_exp HA.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ cons_glu_sub_pred i Γ A SbΓ }} by (econstructor; mauto; reflexivity).
  assert {{ Γ, A ⊩ Type@i : Type@(S i) }} by mauto.
  invert_glu_rel_exp HB.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  rename m into a.
  assert {{ Γ ⊨ Π A B : Type@i }} as [env_relΓ]%rel_exp_of_typ_inversion by mauto using completeness_fundamental_exp.
  assert {{ Γ, A ⊨ B : Type@i }} as [env_relΓA]%rel_exp_of_typ_inversion by mauto using completeness_fundamental_exp.
  destruct_conjs.
  match_by_head1 (per_ctx_env env_relΓA) invert_per_ctx_env.
  pose env_relΓA.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  econstructor; mauto 3; intros Δ' τ **;
    assert {{ Δ' ⊢s τ : Δ }} by mauto 2.
  - assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
    assert (glu_rel_exp_with_sub (S i) Δ' A {{{ Type @ i }}} {{{ σ ∘ τ }}} ρ) as [] by mauto.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    autorewrite with mcltt.
    mauto 3.
  - rename a0 into c.
    rename equiv_a into equiv_c.
    assert {{ Dom ρ ↦ c ≈ ρ ↦ c ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
    destruct_by_head per_univ.
    functional_eval_rewrite_clear.
    rename m0 into b.
    assert {{ Δ' ⊢ m : A[σ][τ] }} by mauto 3 using glu_univ_elem_trm_escape.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }} by mauto 2.
    assert {{ Δ' ⊢ B[(σ∘τ),,m] ≈ B[q σ][τ,,m] : Type@i }} as <- by mauto 2 using sub_decompose_q_typ.
    assert {{ Δ' ⊢s (σ∘τ),,m ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A SbΓ }} as Hconspred by mauto 2.
    (on_all_hyp: fun H => destruct (H _ _ _ Hconspred)).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mcltt.

Lemma glu_rel_exp_of_pi : forall {Γ M A B i Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊨ Π A B : Type@i }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (P : glu_typ_pred) (El : glu_exp_pred), {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ M[σ] : (Π A B)[σ] ® m ∈ El }}) ->
    {{ Γ ⊩ M : Π A B }}.
Proof.
  intros * ? [env_relΓ] Hbody.
  destruct_conjs.
  eexists; split; mauto.
  eexists; intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  simplify_evals.
  eapply mk_glu_rel_exp_with_sub''; mauto.
Qed.

Lemma glu_rel_exp_fn : forall {Γ M A B},
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Proof.
  intros * HM.
  assert {{ Γ, A ⊢ M : B }} by mauto 3.
  assert {{ ⊩ Γ, A }} as [SbΓA] by mauto 3.
  assert (exists i, {{ Γ, A ⊩ B : Type@i }}) as [i] by mauto 3.
  invert_glu_rel_exp HM.
  destruct_conjs.
  match_by_head (glu_ctx_env SbΓA) invert_glu_ctx_env.
  rename TSb into SbΓ.
  rename i0 into j.
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  assert {{ Γ, A ⊨ M : B }} as [env_relΓA] by mauto using completeness_fundamental_exp.
  destruct_conjs.
  pose env_relΓA.
  match_by_head (per_ctx_env env_relΓA) invert_per_ctx_env.
  rename tail_rel into env_relΓ.
  apply_relation_equivalence.
  assert {{ Γ ⊨ Π A B : Type@(max j i) }} by (mauto using completeness_fundamental_exp).
  eapply glu_rel_exp_of_pi; mauto.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_rel_typ.
  destruct_glu_rel_typ_with_sub.
  handle_per_univ_elem_irrel.
  do 2 eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_per_univ_elem_irrel.
  apply_predicate_equivalence.
  match_by_head1 per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  apply_relation_equivalence.
  assert {{ Δ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 4.
  econstructor; mauto 4 using lift_exp_max_left, lift_exp_max_right.
  - intros.
    assert {{ Dom ρ ↦ c ≈ ρ ↦ c' ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA) as [? [[] []]]).
    handle_per_univ_elem_irrel.
    econstructor; mauto.
  - intros.
    eapply glu_univ_elem_typ_monotone; mauto.
    eapply glu_univ_elem_typ_cumu_max_left; revgoals; mauto 4.
  - intros.
    rename b into c.
    rename equiv_b into equiv_c.
    assert {{ Dom ρ ↦ c ≈ ρ ↦ c ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; unshelve eexists; mauto 4).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA) as [? [[] []]]).
    handle_per_univ_elem_irrel.
    eexists; split; mauto.
    rename a0 into b.
    assert {{ DG b ∈ glu_univ_elem (max j i) ↘ OP c equiv_c ↘ OEl c equiv_c }} by mauto.
    assert {{ Δ0 ⊢s σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢ m' : A[σ][σ0] }} by mauto 3 using glu_univ_elem_trm_escape.
    assert {{ Δ0 ⊢ m' : A[σ∘σ0] }} by mauto 3.
    assert {{ Γ, A ⊢ B : Type@(max j i) }} by mauto 2 using lift_exp_max_right.
    assert {{ Δ0 ⊢ B[(σ∘σ0),,m'] ≈ B[q σ][(σ0,,m')] : Type@(max j i) }} as <- by mauto 2 using sub_decompose_q_typ.
    assert {{ Δ0 ⊢ (λ A M)[σ][σ0] m' ≈ M[(σ∘σ0),,m'] : B[σ∘σ0,,m'] }} as ->.
    {
      assert {{ Δ0 ⊢s σ∘σ0 : Γ }} by mauto 3.
      assert {{ Γ ⊢ A : Type@(max j i) }} by mauto 2 using lift_exp_max_left.
      assert {{ Δ0, A[σ∘σ0] ⊢ M[q (σ∘σ0)] : B[q (σ∘σ0)] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A M)[σ∘σ0] : (Π A B)[σ∘σ0] }} by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) : (Π A B)[σ∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) : Π A[σ∘σ0] B[q (σ∘σ0)] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] m' ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) m' : B[q (σ∘σ0)][Id,,m'] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] m' ≈ M[q (σ∘σ0)][Id,,m'] : B[q (σ∘σ0)][Id,,m'] }} by mauto 3.
      assert {{ Δ0 ⊢s Id,,m' : Δ0, A[σ∘σ0] }} by mauto 3.
      assert {{ Δ0, A[σ∘σ0] ⊢s q (σ∘σ0) : Γ, A }} by mauto 2.
      assert {{ Δ0 ⊢s q (σ∘σ0)∘(Id,,m') : Γ, A }} by mauto 2.
      assert {{ Δ0 ⊢s q (σ∘σ0)∘(Id,,m') ≈ σ∘σ0,,m' : Γ, A }} by mauto 2.
      assert {{ Δ0 ⊢ B[q (σ∘σ0)∘(Id,,m')] ≈ B[σ∘σ0,,m'] : Type@i }} as <- by mauto 2.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] m' ≈ M[q (σ∘σ0)][Id,,m'] : B[q (σ∘σ0)∘(Id,,m')] }} as -> by mauto 3.
      assert {{ Δ0 ⊢ M[q (σ∘σ0)][Id,,m'] ≈ M[q (σ∘σ0)∘(Id,,m')] : B[q (σ∘σ0)∘(Id,,m')] }} as -> by mauto 3.
      mauto 3.
    }
    assert {{ Δ0 ⊢ m' : A[σ][σ0] ® c ∈ El }}
      by (eapply glu_univ_elem_exp_lower_max_left; mauto 2; eapply glu_univ_elem_typ_monotone; mauto).
    assert {{ Δ0 ⊢s (σ∘σ0),,m' ® ρ ↦ c ∈ SbΓA }} as HSbΓA by (apply_predicate_equivalence; mauto 2).
    (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
    eapply glu_univ_elem_exp_cumu_max_right; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_fn : mcltt.

Lemma glu_rel_exp_app : forall {Γ M N A B i},
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Proof.
  intros * HB HM HN.
  assert {{ ⊩ Γ, A }} as [SbΓA] by mauto 3.
  match_by_head (glu_ctx_env SbΓA) invert_glu_ctx_env.
  apply_predicate_equivalence.
  rename i0 into j.
  rename TSb into SbΓ.
  assert {{ Γ, A ⊩ Type@i : Type@(S i) }} by mauto 3.
  assert {{ Γ, A ⊩ B : Type@i }} by mauto 4.
  invert_glu_rel_exp HB.
  destruct_conjs.
  assert {{ Γ ⊩ A : Type@j }} by (eexists; intuition; eexists; mauto 4).
  assert {{ Γ ⊩ Type@(max i j) : Type@(S (max i j)) }} by mauto 3.
  assert {{ Γ, A ⊩ Type@(max i j) : Type@(S (max i j)) }} by mauto 3.
  assert (j <= max i j) by lia.
  assert {{ Γ ⊩ A : Type@(max i j) }} by mauto 4.
  assert (i <= max i j) by lia.
  assert {{ Γ, A ⊩ B : Type@(max i j) }} by mauto 4.
  assert {{ Γ ⊩ Π A B : Type@(max i j) }} by mauto 3.
  assert {{ Γ, A ⊢ B : Type@(max i j) }} by mauto 2.
  assert {{ Γ ⊢ M : Π A B }} by mauto 3.
  assert {{ Γ ⊢ N : A }} by mauto 3.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HN.
  eexists; split; [eassumption |].
  eexists.
  intros.
  destruct_glu_rel_typ_with_sub.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m into n.
  rename m0 into m.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  inversion_clear_by_head pi_glu_exp_pred.
  assert {{ Dom a ≈ a ∈ per_univ (max i j) }} as [] by mauto.
  handle_per_univ_elem_irrel.
  assert {{ Dom n ≈ n ∈ in_rel }} by (eapply glu_univ_elem_per_elem; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  simplify_evals.
  rename a0 into b.
  rename fa into mn.
  eapply mk_glu_rel_exp_with_sub''; mauto using per_univ_elem_cumu_max_right.
  intros.
  match_by_head1 (in_rel n n) ltac:(fun H => rename H into equiv_n).
  assert {{ DG b ∈ glu_univ_elem (max i j) ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
  assert {{ Δ ⊢ A[σ] ® P0 }} by (eapply glu_univ_elem_trm_typ; eassumption).
  assert {{ Δ ⊢w Id : Δ }} by mauto 3.
  assert {{ Δ ⊢ IT[Id] ® P0 }} by mauto 2.
  assert {{ Δ ⊢ IT[Id] : Type@(max i j) }} by (eapply glu_univ_elem_univ_lvl; revgoals; eassumption).
  assert {{ Δ ⊢ IT : Type@(max i j) }} by mauto 2.
  assert {{ Δ ⊢ IT[Id] ≈ A[σ] : Type@(max i j) }} as HAeq by (eapply glu_univ_elem_typ_unique_upto_exp_eq'; revgoals; eassumption).
  assert {{ Δ ⊢ N[σ] : IT[Id] ® n ∈ El0 }} by (rewrite HAeq; eassumption).
  assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ][Id] N[σ] : OT[Id,,N[σ]] ® mn ∈ OEl n equiv_n }}) as [] by mauto 2.
  destruct_conjs.
  functional_eval_rewrite_clear.
  assert {{ Δ ⊢ N[σ] : A[σ][Id] ® n ∈ El }}
    by (autorewrite with mcltt; eapply glu_univ_elem_exp_conv; [| | eassumption | eassumption |]; mauto 3).
  assert {{ Δ ⊢s σ∘Id,,N[σ] ® ρ ↦ n ∈ cons_glu_sub_pred j Γ A SbΓ }} as Hcons by (apply_predicate_equivalence; mauto 2).
  (on_all_hyp: destruct_glu_rel_by_assumption (cons_glu_sub_pred j Γ A SbΓ)).
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 2.
  assert {{ Γ ⊢s Id,,N : Γ, A }} by mauto 2.
  assert {{ Δ ⊢ N[σ] : A[σ] }} by mauto 3.
  assert {{ Δ ⊢s Id,,N[σ] : Δ, A[σ] }} by mauto 3.
  assert {{ Δ ⊢s σ ≈ σ∘Id : Γ }} by mauto 3.
  assert {{ Δ ⊢s σ,,N[σ] ≈ (σ∘Id),,N[σ] : Γ, A }} by mauto 3.
  assert {{ Δ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Γ, A }} by mauto 2.
  autorewrite with mcltt.
  assert {{ Δ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Type@(max i j) }} as -> by mauto 3.
  assert {{ Δ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as -> by mauto 3.
  assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as <-.
  {
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : (Π A B)[σ] }} by mauto 2.
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : Π A[σ] B[q σ] }} by mauto 3.
    let H := fresh "H" in
    assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[q σ][Id,,N[σ]] }} as H by mauto 3;
    autorewrite with mcltt in H; mauto 3.
  }
  assert {{ Δ ⊢ B[σ,,N[σ]] ≈ B[(σ∘Id),,N[σ]] : Type@(max i j) }} as -> by mauto 3.
  assert {{ Δ ⊢ B[(σ∘Id),,N[σ]] ≈ OT[Id,,N[σ]] : Type@(max i j) }} as ->.
  {
    assert {{ Δ ⊢ OT[Id,,N[σ]] ® OP n equiv_n }} by (eapply glu_univ_elem_trm_typ; eassumption).
    replace (max i j) with (max i (max i j)) by lia.
    eapply glu_univ_elem_typ_unique_upto_exp_eq; revgoals; eassumption.
  }
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_app : mcltt.
