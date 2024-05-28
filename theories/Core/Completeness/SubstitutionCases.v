From Coq Require Import Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.ContextCases Completeness.LogicalRelation System.
Import Domain_Notations.

Lemma rel_sub_id : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨s Id ≈ Id : Γ }}.
Proof with mautosolve.
  intros * [].
  eexists_rel_sub...
Qed.

#[export]
Hint Resolve rel_sub_id : mcltt.

Lemma rel_sub_weaken : forall {Γ A},
    {{ ⊨ Γ, A }} ->
    {{ Γ, A ⊨s Wk ≈ Wk : Γ }}.
Proof with intuition.
  intros * [env_relΓA].
  inversion_by_head (per_ctx_env env_relΓA); subst.
  eexists_rel_sub.
  econstructor; only 1-2: repeat econstructor...
Qed.

#[export]
Hint Resolve rel_sub_weaken : mcltt.

Lemma rel_sub_compose_cong : forall {Γ τ τ' Γ' σ σ' Γ''},
    {{ Γ ⊨s τ ≈ τ' : Γ' }} ->
    {{ Γ' ⊨s σ ≈ σ' : Γ'' }} ->
    {{ Γ ⊨s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΓ']]] [].
  destruct_conjs.
  pose (env_relΓ'0 := env_relΓ').
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ')...
Qed.

#[export]
Hint Resolve rel_sub_compose_cong : mcltt.

Lemma rel_sub_extend_cong : forall {i Γ M M' σ σ' Δ A},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A[σ] }} ->
    {{ Γ ⊨s σ ,, M ≈ σ' ,, M' : Δ, A }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΔ]]] HA [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΔ0 := env_relΔ).
  assert {{ ⊨ Δ, A }} as [env_relΔA] by (eapply rel_ctx_extend; eauto; eexists; eassumption).
  destruct_conjs.
  pose (env_relΔA0 := env_relΔA).
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  match_by_head (per_ctx_env env_relΔA) invert_per_ctx_env.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ A[σ] }}}); subst.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp...
Qed.

#[export]
Hint Resolve rel_sub_extend_cong : mcltt.

Lemma rel_sub_id_compose_right : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨s Id ∘ σ ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_right : mcltt.

Lemma rel_sub_id_compose_left : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨s σ ∘ Id ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_left : mcltt.

Lemma rel_sub_compose_assoc : forall {Γ σ Γ' σ' Γ'' σ'' Γ'''},
    {{ Γ' ⊨s σ : Γ }} ->
    {{ Γ'' ⊨s σ' : Γ' }} ->
    {{ Γ''' ⊨s σ'' : Γ'' }} ->
    {{ Γ''' ⊨s (σ ∘ σ') ∘ σ'' ≈ σ ∘ (σ' ∘ σ'') : Γ }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ' [? [env_relΓ]]] [env_relΓ'' [? []]] [env_relΓ'''].
  destruct_conjs.
  pose (env_relΓ'0 := env_relΓ').
  pose (env_relΓ''0 := env_relΓ'').
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ''').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_compose_assoc : mcltt.

Lemma rel_sub_extend_compose : forall {Γ τ Γ' M σ Γ'' A i},
    {{ Γ' ⊨s σ : Γ'' }} ->
    {{ Γ'' ⊨ A : Type@i }} ->
    {{ Γ' ⊨ M : A[σ] }} ->
    {{ Γ ⊨s τ : Γ' }} ->
    {{ Γ ⊨s (σ ,, M) ∘ τ ≈ (σ ∘ τ) ,, M[τ] : Γ'', A }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ' [? [env_relΓ'']]] HA [] [env_relΓ].
  destruct_conjs.
  pose (env_relΓ'0 := env_relΓ').
  pose (env_relΓ''0 := env_relΓ'').
  assert {{ ⊨ Γ'', A }} as [env_relΓ''A] by (eapply rel_ctx_extend; eauto; eexists; eassumption).
  destruct_conjs.
  pose (env_relΓ''A0 := env_relΓ''A).
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  match_by_head (per_ctx_env env_relΓ''A) invert_per_ctx_env.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ A[σ] }}}); subst.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend_compose : mcltt.

Lemma rel_sub_p_extend : forall {Γ' M σ Γ A},
    {{ Γ' ⊨s σ : Γ }} ->
    {{ Γ' ⊨ M : A[σ] }} ->
    {{ Γ' ⊨s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ' [? [env_relΓ]]] [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΓ'0 := env_relΓ').
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ A[σ] }}}); subst.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_p_extend : mcltt.

Lemma rel_sub_extend : forall {Γ' σ Γ A},
    {{ Γ' ⊨s σ : Γ, A }} ->
    {{ Γ' ⊨s σ ≈ (Wk ∘ σ) ,, #0[σ] : Γ, A }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ' [? [env_relΓA]]].
  destruct_conjs.
  pose (env_relΓA0 := env_relΓA).
  pose (env_relΓ'0 := env_relΓ').
  inversion_by_head (per_ctx_env env_relΓA); subst.
  rename tail_rel into env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend : mcltt.

Lemma rel_sub_sym : forall {Γ σ σ' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  assert (env_relΓ p' p) by (symmetry; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto; symmetry...
Qed.

#[export]
Hint Resolve rel_sub_sym : mcltt.

Lemma rel_sub_trans : forall {Γ σ σ' σ'' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ'' : Δ }} ->
    {{ Γ ⊨s σ ≈ σ'' : Δ }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  assert (env_relΓ p' p') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  functional_eval_rewrite_clear.
  econstructor; mauto; etransitivity...
Qed.

#[export]
Hint Resolve rel_sub_trans : mcltt.

#[export]
Instance rel_sub_PER {Γ A} : PER (rel_sub_under_ctx Γ A).
Proof.
  split; mauto.
Qed.

Lemma rel_sub_conv : forall {Γ σ σ' Δ Δ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⊨ Δ ≈ Δ' }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ' }}.
Proof with mautosolve.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ [? [env_relΔ]]] [].
  destruct_conjs.
  pose (env_relΔ0 := env_relΔ).
  handle_per_ctx_env_irrel.
  assert {{ EF Δ' ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_conv : mcltt.

Lemma presup_rel_sub : forall {Γ σ σ' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⊨ Γ }} /\ {{ Γ ⊨s σ : Δ }} /\ {{ Γ ⊨s σ' : Δ }} /\ {{ ⊨ Δ }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]].
  destruct_conjs.
  repeat split; try solve [eexists; eauto];
    unfold valid_sub_under_ctx;
    etransitivity; only 2,3: symmetry;
    econstructor...
Qed.
