From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation Readback.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env : ctx -> env -> Prop :=
| initial_env_nil : initial_env nil empty_env
| initial_env_cons :
  `( initial_env Γ p ->
     {{ ⟦ A ⟧ p ↘ a }} ->
     initial_env (A :: Γ) d{{{ p ↦ ⇑! a (length Γ) }}}).

#[export]
Hint Constructors initial_env : mcltt.

Lemma functional_initial_env : forall Γ p,
    initial_env Γ p ->
    forall p',
      initial_env Γ p' ->
      p = p'.
Proof.
  induction 1; intros ? Hother; inversion_clear Hother; eauto.
  erewrite IHinitial_env in *; try eassumption;
    functional_eval_rewrite_clear;
    eauto.
Qed.

#[export]
Hint Resolve functional_initial_env : mcltt.

Ltac functional_initial_env_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_initial_env equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : initial_env ?G ?p, H2 : initial_env ?G ?p' |- _ =>
      clean replace p' with p by first [solve [mauto] | tactic_error p' p]; clear H2
  end.
Ltac functional_initial_env_rewrite_clear := repeat functional_initial_env_rewrite_clear1.

Inductive nbe : ctx -> exp -> typ -> nf -> Prop :=
| nbe_run :
  `( initial_env Γ p ->
     {{ ⟦ A ⟧ p ↘ a }} ->
     {{ ⟦ M ⟧ p ↘ m }} ->
     {{ Rnf ⇓ a m in (length Γ) ↘ w }} ->
     nbe Γ M A w ).

#[export]
Hint Constructors nbe : mcltt.

Lemma functional_nbe : forall Γ M A w w',
    nbe Γ M A w ->
    nbe Γ M A w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.
