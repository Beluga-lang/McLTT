From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export Domain Evaluation Readback.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env : ctx -> env -> Prop :=
| initial_env_nil : initial_env nil empty_env
| initial_env_cons :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     initial_env (A :: Γ) d{{{ ρ ↦ ⇑! a (length Γ) }}}).

#[export]
Hint Constructors initial_env : mcltt.

Lemma functional_initial_env : forall Γ ρ,
    initial_env Γ ρ ->
    forall ρ',
      initial_env Γ ρ' ->
      ρ = ρ'.
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
  | H1 : initial_env ?G ?ρ, H2 : initial_env ?G ?ρ' |- _ =>
      clean replace ρ' with ρ by first [solve [mauto 2] | tactic_error ρ' ρ]; clear H2
  end.
Ltac functional_initial_env_rewrite_clear := repeat functional_initial_env_rewrite_clear1.

Inductive nbe : ctx -> exp -> typ -> nf -> Prop :=
| nbe_run :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
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

#[export]
Hint Resolve functional_nbe : mcltt.

Lemma nbe_cumu : forall {Γ A i W},
    nbe Γ A {{{ Type@i }}} W ->
    nbe Γ A {{{ Type@(S i) }}} W.
Proof.
  inversion_clear 1.
  simplify_evals.
  inversion_clear_by_head read_nf.
  mauto.
Qed.

Lemma lift_nbe_ge : forall {Γ A i j W},
    i <= j ->
    nbe Γ A {{{ Type@i }}} W ->
    nbe Γ A {{{ Type@j }}} W.
Proof.
  induction 1; mauto using nbe_cumu.
Qed.

Lemma lift_nbe_max_left : forall {Γ A i i' W},
    nbe Γ A {{{ Type@i }}} W ->
    nbe Γ A {{{ Type@(max i i') }}} W.
Proof.
  intros.
  assert (i <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

Lemma lift_nbe_max_right : forall {Γ A i i' W},
    nbe Γ A {{{ Type@i' }}} W ->
    nbe Γ A {{{ Type@(max i i') }}} W.
Proof.
  intros.
  assert (i' <= max i i') by lia.
  mauto using lift_nbe_ge.
Qed.

#[export]
Hint Resolve lift_nbe_max_left lift_nbe_max_right : mcltt.

Lemma functional_nbe_of_typ : forall Γ A i j W W',
    nbe Γ A {{{ Type@i }}} W ->
    nbe Γ A {{{ Type@j }}} W' ->
    W = W'.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_of_typ : mcltt.


Inductive nbe_ty : ctx -> typ -> nf -> Prop :=
| nbe_ty_run :
  `( initial_env Γ ρ ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Rtyp m in (length Γ) ↘ W }} ->
     nbe_ty Γ M W ).

#[export]
Hint Constructors nbe_ty : mcltt.

Lemma functional_nbe_ty : forall Γ M w w',
    nbe_ty Γ M w ->
    nbe_ty Γ M w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

Lemma nbe_type_to_nbe_ty : forall Γ M i w,
    nbe Γ M {{{ Type@i }}} w ->
    nbe_ty Γ M w.
Proof.
  intros. progressive_inversion.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_ty nbe_type_to_nbe_ty : mcltt.

Ltac functional_nbe_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_nbe equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : nbe ?G ?M ?A ?W, H2 : nbe ?G ?M ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?G ?A {{{ Type@?i }}} ?W, H2 : nbe ?G ?A {{{ Type@?j }}} ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]
  | H1 : nbe_ty ?G ?M ?W, H2 : nbe_ty ?G ?M ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  end.
Ltac functional_nbe_rewrite_clear := repeat functional_nbe_rewrite_clear1.
