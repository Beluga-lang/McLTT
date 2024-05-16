From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.


Inductive eval_exp_order : exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order {{{ Type@i }}} p )
| eeo_var :
  `( eval_exp_order {{{ # x }}} p )
| eeo_nat :
  `( eval_exp_order {{{ ℕ }}} p )
| eeo_zero :
  `( eval_exp_order {{{ zero }}} p )
| eeo_succ :
  `( eval_exp_order {{{ M }}} p ->
     eval_exp_order {{{ succ M }}} p )
| eeo_natrec :
  `( eval_exp_order M p ->
     (forall m, {{ ⟦ M ⟧ p ↘ m }} -> eval_natrec_order A MZ MS m p) ->
     eval_exp_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} p )
| eeo_pi :
  `( eval_exp_order A p ->
     eval_exp_order {{{ Π A B }}} p )
| eeo_fn :
  `( eval_exp_order {{{ λ A M }}} p )
| eeo_app :
  `( eval_exp_order M p ->
     eval_exp_order N p ->
     (forall m n, {{ ⟦ M ⟧ p ↘ m }} -> {{ ⟦ N ⟧ p ↘ n }} -> eval_app_order m n) ->
     eval_exp_order {{{ M N }}} p )
| eeo_sub :
  `( eval_sub_order σ p ->
     (forall p', {{ ⟦ σ ⟧s p ↘ p' }} -> eval_exp_order M p') ->
     eval_exp_order {{{ M[σ] }}} p )

with eval_natrec_order : exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order MZ p ->
     eval_natrec_order A MZ MS d{{{ zero }}} p )
| eno_succ :
  `( eval_natrec_order A MZ MS b p ->
     (forall r, {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} -> eval_exp_order {{{ MS }}} d{{{ p ↦ b ↦ r }}}) ->
     eval_natrec_order A MZ MS d{{{ succ b }}} p )
| eno_neut :
  `( eval_exp_order MZ p ->
     eval_exp_order A d{{{ p ↦ ⇑ ℕ m }}} ->
     eval_natrec_order A MZ MS d{{{ ⇑ ℕ m }}} p )

with eval_app_order : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order M d{{{ p ↦ n }}} ->
     eval_app_order d{{{ λ p M }}} n )
| eao_neut :
  `( eval_exp_order B d{{{ p ↦ n }}} ->
     eval_app_order d{{{ ⇑ (Π a p B) m }}} n )

with eval_sub_order : sub -> env -> Prop :=
| eso_id :
  `( eval_sub_order {{{ Id }}} p )
| eso_weaken :
  `( eval_sub_order {{{ Wk }}} p )
| eso_extend :
  `( eval_sub_order σ p ->
     eval_exp_order M p ->
     eval_sub_order {{{ σ ,, M }}} p )
| eso_compose :
  `( eval_sub_order τ p ->
     (forall p', {{ ⟦ τ ⟧s p ↘ p' }} -> eval_sub_order σ p') ->
     eval_sub_order {{{ σ ∘ τ }}} p ).

#[local]
  Hint Constructors eval_exp_order eval_natrec_order eval_app_order eval_sub_order : mcltt.


Lemma eval_exp_order_sound : forall m p a,
    {{ ⟦ m ⟧ p ↘ a }} ->
    eval_exp_order m p
with eval_natrec_order_sound : forall A MZ MS m p r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
    eval_natrec_order A MZ MS m p
with eval_app_order_sound: forall m n r,
  {{ $| m & n |↘ r }} ->
  eval_app_order m n
with eval_sub_order_sound: forall σ p p',
  {{ ⟦ σ ⟧s p ↘ p' }} ->
  eval_sub_order σ p.
Proof with (econstructor; intros; functional_eval_rewrite_clear; eauto).
  - clear eval_exp_order_sound; induction 1...
  - clear eval_natrec_order_sound; induction 1...
  - clear eval_app_order_sound; induction 1...
  - clear eval_sub_order_sound; induction 1...
Qed.
