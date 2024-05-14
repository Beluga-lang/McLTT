From Mcltt Require Import Base.
From Mcltt Require Import Evaluation.Definitions.
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
  `( {{ eval_exp_order M p }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
     eval_exp_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} p ).

| eval_exp_natrec :
  `( {{ ⟦ M ⟧ p ↘ m }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
     {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ p ↘ r }} )
| eval_exp_pi :
  `( {{ ⟦ A ⟧ p ↘ a }} ->
     {{ ⟦ Π A B ⟧ p ↘ Π a p B }} )
| eval_exp_fn :
  `( {{ ⟦ λ A M ⟧ p ↘ λ p M }} )
| eval_exp_app :
  `( {{ ⟦ M ⟧ p ↘ m }} ->
     {{ ⟦ N ⟧ p ↘ n }} ->
     {{ $| m & n |↘ r }} ->
     {{ ⟦ M N ⟧ p ↘ r }} )
| eval_exp_sub :
  `( {{ ⟦ σ ⟧s p ↘ p' }} ->
     {{ ⟦ M ⟧ p' ↘ m }} ->
     {{ ⟦ M[σ] ⟧ p ↘ m }} )
