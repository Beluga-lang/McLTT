From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Semantic Require Export NbE.
From Mcltt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  rename x into elem_rel.
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable...
Qed.

Lemma completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.

Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall M N,
    not_univ_pi M ->
    M = N ->
    {{ ⊢anf M ⊆ N }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π A B ⊆ Π A' B' }}
where "⊢anf M ⊆ N" := (alg_subtyping_nf M N) (in custom judg) : type_scope.

From Mcltt.Core.Syntactic Require Export CtxSub.

Lemma completeness_subtyp : forall {Γ A A'},
    {{ Γ ⊢ A ⊆ A' }} ->
    forall Γ',
      {{ ⊢ Γ' ⊆ Γ }} ->
      exists W W', nbe_ty Γ' A W /\ nbe_ty Γ A' W' /\ {{ ⊢anf W ⊆ W' }}.
Proof.
  intros * HA ? HG.
  assert {{ Γ' ⊢ A ⊆ A' }} as HA' by mauto 3.
  eapply completeness_fundamental_subtyp in HA as [env_relΓ].
  eapply completeness_fundamental_subtyp in HA' as [env_relΓ'].
  destruct_conjs.
  eapply completeness_fundamental_ctx_subtyp in HG.
  assert (exists p p', initial_env Γ' p /\ initial_env Γ' p' /\ {{ Dom p ≈ p' ∈ env_relΓ' }}) as [p] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Dom p ≈ p ∈ env_relΓ }} by (eapply per_ctx_env_subtyping; mauto 2).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  rename x into elem_rel.
  rename x0 into elem_rel'.
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  functional_eval_rewrite_clear.
  do 2 eexists.
  repeat split; only 1-2: econstructor; try eassumption.
  - admit. (* {{ Rtyp a2 in length Γ' ↘ ~ ?W }} *) (* We need "realizability" of subtyping *)
  - admit. (* initial_env Γ p *) (* We need a relation between initial environments of super/sub-context pair *)
  - admit. (* {{ Rtyp a1 in length Γ ↘ ~ ?W' }} *) (* We need "realizability" of subtyping *)
  - admit. (* {{ ⊢anf ~ ?W ⊆ ~ ?W' }} *) (* We need "realizability" of subtyping *)
Abort.
