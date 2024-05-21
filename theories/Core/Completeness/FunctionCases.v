From Coq Require Import Morphisms_Relations Relation_Definitions RelationClasses.
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

Lemma rel_exp_pi_core : forall {i p o B p' o' B'} {tail_rel : relation env}
    (head_rel : forall p p', {{ Dom p ≈ p' ∈ tail_rel }} -> relation domain)
    (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }})
    {out_rel},
    (forall c c',
        head_rel p p' equiv_p_p' c c' ->
        rel_exp B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (per_univ i)) ->
    (* We use this equality to make unification on `out_rel` works *)
    (out_rel = fun c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c') m m' =>
                 forall b b' R,
                   {{ ⟦ B ⟧ o ↦ c ↘ b }} ->
                   {{ ⟦ B' ⟧ o' ↦ c' ↘ b' }} ->
                   per_univ_elem i R b b' -> R m m') ->
    (forall c c' (equiv_c_c' : head_rel p p' equiv_p_p' c c'), rel_typ i B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')).
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros.
  subst.
  (on_all_hyp: destruct_rel_by_assumption (head_rel p p' equiv_p_p')).
  destruct_by_head rel_exp.
  econstructor; mauto.
  destruct_by_head per_univ.
  apply -> per_univ_elem_morphism_iff; eauto.
  split; intros; handle_per_univ_elem_irrel...
Qed.

Lemma rel_exp_pi_cong : forall {i Γ A A' B B'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊨ B ≈ B' : Type@i }} ->
    {{ Γ ⊨ Π A B ≈ Π A' B' : Type@i }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓA].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΓA0 := env_relΓA).
  inversion_by_head (per_ctx_env env_relΓA); subst.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists (per_univ _).
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  eexists.
  per_univ_elem_econstructor; eauto with typeclass_instances.
  - intros.
    eapply rel_exp_pi_core; eauto.
    + clear dependent c.
      clear dependent c'.
      intros.
      extract_output_info_with p c p' c' env_relΓA.
      invert_rel_typ_body.
      econstructor...
    + reflexivity.
  - (* `reflexivity` does not work as (simple) unification fails for some unknown reason. *)
    apply Equivalence_Reflexive.
Qed.

Lemma rel_exp_pi_sub : forall {i Γ σ Δ A B},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ , A ⊨ B : Type@i }} ->
    {{ Γ ⊨ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@i }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [] [env_relΔA].
  destruct_conjs.
  pose (env_relΔA0 := env_relΔA).
  inversion_by_head (per_ctx_env env_relΔA); subst.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  assert {{ Dom o' ≈ o' ∈ tail_rel }} by (etransitivity; [symmetry|]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  eexists.
  per_univ_elem_econstructor; eauto with typeclass_instances.
  - intros.
    eapply rel_exp_pi_core; eauto.
    + clear dependent c.
      clear dependent c'.
      intros.
      extract_output_info_with o c o' c' env_relΔA.
      invert_rel_typ_body.
      destruct_conjs.
      econstructor; eauto.
      repeat econstructor...
    + reflexivity.
  - (* `reflexivity` does not work as (simple) unification fails for some unknown reason. *)
    apply Equivalence_Reflexive.
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
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  - per_univ_elem_econstructor; [eapply per_univ_elem_cumu_max_left | | |];
      eauto with typeclass_instances.
    + intros.
      eapply rel_exp_pi_core; eauto.
      * clear dependent c.
        clear dependent c'.
        intros.
        extract_output_info_with p c p' c' env_relΓA.
        econstructor; eauto.
        eexists.
        eapply per_univ_elem_cumu_max_right...
      * reflexivity.
    + (* `reflexivity` does not work as it uses a "wrong" instance. *)
      apply Equivalence_Reflexive.
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
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  - per_univ_elem_econstructor; [eapply per_univ_elem_cumu_max_left | | |];
      eauto with typeclass_instances.
    + intros.
      eapply rel_exp_pi_core; eauto.
      * clear dependent c.
        clear dependent c'.
        intros.
        extract_output_info_with o c o' c' env_relΔA.
        econstructor; eauto.
        eexists.
        eapply per_univ_elem_cumu_max_right...
      * reflexivity.
    + (* `reflexivity` does not work as it uses a "wrong" instance. *)
      apply Equivalence_Reflexive.
  - intros ? **.
    extract_output_info_with o c o' c' env_relΔA.
    econstructor; only 1-2: repeat econstructor; simpl; mauto.
    intros.
    handle_per_univ_elem_irrel...
Qed.

Lemma rel_exp_app_cong : forall {Γ M M' A B N N'},
    {{ Γ ⊨ M ≈ M' : Π A B }} ->
    {{ Γ ⊨ N ≈ N' : A }} ->
    {{ Γ ⊨ M N ≈ M' N' : B[Id,,N] }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (equiv_p'_p' : env_relΓ p' p') by (etransitivity; [symmetry |]; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  invert_rel_typ_body.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  assert (in_rel0 m1 m2) by (etransitivity; [| symmetry]; eauto).
  assert (in_rel m1 m'2) by intuition.
  assert (in_rel m1 m2) by intuition.
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  (on_all_hyp: destruct_rel_by_assumption in_rel0).
  (on_all_hyp_rev: destruct_rel_by_assumption in_rel0).
  handle_per_univ_elem_irrel.
  eexists.
  split; [> econstructor; only 1-2: econstructor ..].
  1,3: repeat econstructor.
  all: intuition.
Qed.

Lemma rel_exp_app_sub : forall {Γ σ Δ M A B N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ M : Π A B }} ->
    {{ Δ ⊨ N : A }} ->
    {{ Γ ⊨ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ] [env_relΔ] [env_relΔ'].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΔ0 := env_relΔ).
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  (on_all_hyp_rev: destruct_rel_by_assumption in_rel).
  eexists.
  split; [> econstructor; only 1-2: econstructor ..].
  1,3,8,9: repeat econstructor.
  15: econstructor.
  all: eauto.
Qed.

Lemma rel_exp_pi_beta : forall {Γ A M B N},
  {{ Γ , A ⊨ M : B }} ->
  {{ Γ ⊨ N : A }} ->
  {{ Γ ⊨ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓA] [env_relΓ].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  pose (env_relΓA0 := env_relΓA).
  inversion_by_head (per_ctx_env env_relΓA); subst.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption tail_rel).
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  rename m into n; rename m' into n'.
  extract_output_info_with p n p' n' env_relΓA.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
Qed.

Lemma rel_exp_pi_eta : forall {Γ M A B},
  {{ Γ ⊨ M : Π A B }} ->
  {{ Γ ⊨ M ≈ λ A (M[Wk] #0) : Π A B }}.
Proof with intuition.
  pose proof (@relation_equivalence_pointwise domain).
  pose proof (@relation_equivalence_pointwise env).
  intros * [env_relΓ].
  destruct_conjs.
  pose (env_relΓ0 := env_relΓ).
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  intros.
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  econstructor; eauto.
  do 2 econstructor; eauto; econstructor; eauto.
  econstructor.
Qed.
