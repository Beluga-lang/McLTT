From Mcltt Require Import Base LibTactics LogicalRelation.
Import Domain_Notations.

Lemma valid_typ : forall {i Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ Type@i : Type@(S i) }}.
Proof.
  intros * [].
  econstructor.
  eexists; try eassumption.
  eexists.
  intros.
  exists (per_univ (S i)).
  unshelve (split; repeat econstructor); mauto.
Qed.

Lemma rel_exp_typ_sub : forall {i Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ Type@i[σ] ≈ Type@i : Type@(S i) }}.
Proof.
  intros * [env_rel].
  destruct_conjs.
  econstructor.
  eexists; try eassumption.
  eexists.
  intros.
  exists (per_univ (S i)).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_rel H).
  unshelve (split; repeat econstructor); only 4: eauto; mauto.
Qed.

Lemma rel_exp_cumu : forall {i Γ A A'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@(S i) }}.
Proof.
  intros * [env_rel].
  destruct_conjs.
  econstructor.
  eexists; try eassumption.
  exists (S (S i)).
  intros.
  exists (per_univ (S i)).
  (on_all_hyp: fun H => destruct_rel_by_assumption env_rel H).
  inversion_by_head rel_typ.
  inversion_by_head rel_exp.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  match_by_head per_univ_elem ltac:(fun H => invert_per_univ_elem H); subst.
  destruct_conjs.
  per_univ_elem_irrel_rewrite.
  match_by_head per_univ_elem ltac:(fun H => apply per_univ_elem_cumu in H).
  split; econstructor; try eassumption; repeat econstructor; mauto.
Qed.
