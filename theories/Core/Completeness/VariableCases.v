From Coq Require Import Relations.
From Mcltt Require Import Base LibTactics LogicalRelation System.
Import Domain_Notations.

Lemma valid_lookup : forall {Γ x A env_rel}
                        (equiv_Γ_Γ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    {{ #x : A ∈ Γ }} ->
    exists i,
    forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_rel }}),
    exists elem_rel,
      rel_typ i A p A p' elem_rel /\ rel_exp elem_rel {{{ #x }}} p {{{ #x }}} p'.
Proof with solve [repeat econstructor; mauto].
  intros.
  assert {{ #x : A ∈ Γ }} as HxinΓ by mauto.
  remember Γ as Δ eqn:HΔΓ in HxinΓ, equiv_Γ_Γ at 2. clear HΔΓ. rename equiv_Γ_Γ into equiv_Γ_Δ.
  remember A as A' eqn:HAA' in HxinΓ |- * at 2. clear HAA'.
  gen Δ A' env_rel.
  induction H; intros * equiv_Γ_Δ H0; inversion H0; subst; clear H0; inversion_clear equiv_Γ_Δ; subst;
    try (specialize (IHctx_lookup _ _ _ equiv_Γ_Γ' H2) as [j ?]; destruct_conjs);
    eexists; intros ? ? [];
    (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H); destruct_conjs;
    eexists.
  - split; econstructor...
  - destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    inversion_by_head (eval_exp {{{ #n }}}); subst.
    split; econstructor; simpl...
Qed.

Lemma valid_var : forall {Γ x A},
    {{ ⊨ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊨ #x : A }}.
Proof.
  intros * [? equiv_Γ_Γ] ?.
  econstructor.
  unshelve epose proof (valid_lookup equiv_Γ_Γ _); mauto.
Qed.

Lemma rel_exp_var_weaken : forall {Γ B x A},
    {{ ⊨ Γ , B }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ , B ⊨ #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof.
  intros * [] HxinΓ.
  match_by_head1 per_ctx_env ltac:(fun H => inversion H); subst.
  unshelve epose proof (valid_lookup _ HxinΓ); revgoals; mauto.
  destruct_conjs.
  eexists.
  eexists; try eassumption.
  eexists.
  intros ? ? [].
  (on_all_hyp: fun H => destruct_rel_by_assumption tail_rel H).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  inversion_by_head (eval_exp {{{ #x }}}); subst.
  eexists.
  split; [> econstructor; only 1-2: repeat econstructor; mauto ..].
Qed.
