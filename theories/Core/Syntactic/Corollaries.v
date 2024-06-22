From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics CtxSub.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Syntax_Notations.

Corollary sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A [ Id ] }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve sub_id_typ : mcltt.

Corollary invert_sub_id : forall Γ M A,
    {{ Γ ⊢ M [ Id ] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcltt.

Add Parametric Morphism i Γ Δ t (H : {{ Δ ⊢ t : Type@i }}) : (a_sub t)
    with signature wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Type@i }}} as sub_typ_cong1.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.
