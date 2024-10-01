From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core Require Export Soundness.
From Mcltt.Core.Completeness.Consequences Require Export Types.
Import Domain_Notations.

Lemma adjust_exp_eq_level : forall {Γ A A' i j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A : Type@j }} ->
    {{ Γ ⊢ A' : Type@j }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  intros * ?%completeness ?%soundness ?%soundness.
  destruct_conjs.
  inversion_by_head nbe; subst.
  match_by_head eval_exp ltac:(fun H => directed inversion H; subst; clear H).
  match_by_head read_nf ltac:(fun H => directed inversion H; subst; clear H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [symmetry|]; mautosolve.
Qed.

Lemma exp_eq_pi_inversion : forall {Γ A B A' B' i},
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} /\ {{ Γ, A ⊢ B ≈ B' : Type@i }}.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply completeness in H).
  (on_all_hyp: fun H => pose proof (soundness H)).
  destruct_conjs.
  dir_inversion_clear_by_head nbe.
  dir_inversion_by_head initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  dir_inversion_by_head read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  match_by_head (@eq nf) ltac:(fun H => directed inversion H; subst; clear H).
  assert {{ Γ ⊢ A ≈ A' : Type@i }} by mauto.
  assert {{ ⊢ Γ, A ≈ Γ, A' }} by mauto.
  split; mauto.
Qed.

Lemma nf_of_pi : forall {Γ M A B},
    {{ Γ ⊢ M : Π A B }} ->
    exists W1 W2, nbe Γ M {{{ Π A B }}} n{{{ λ W1 W2 }}}.
Proof.
  intros * ?%soundness.
  destruct_conjs.
  inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 read_nf ltac:(fun H => inversion_clear H).
  do 2 eexists; mauto.
Qed.

Lemma idempotent_nbe_ty : forall {Γ i A B C},
    {{ Γ ⊢ A : Type@i }} ->
    nbe_ty Γ A B ->
    nbe_ty Γ B C ->
    B = C.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ B : Type@i }} as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.

#[export]
Hint Resolve idempotent_nbe_ty : mcltt.
