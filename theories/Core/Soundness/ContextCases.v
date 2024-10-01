From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_ctx_empty : {{ ⊩ ⋅ }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcltt.

Lemma glu_rel_ctx_extend : forall {Γ A i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ ⊩ Γ, A }}.
Proof.
  intros * [Sb] HA.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcltt.
