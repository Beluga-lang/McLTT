From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export System.
Import Syntax_Notations.

Lemma wf_univ_inversion : forall {Γ i A},
    {{ Γ ⊢ Type@i : A }} ->
    {{ Γ ⊢ Type@(S i) ⊆ A }}.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_univ_inversion : mcltt.

Lemma wf_nat_inversion : forall Γ A,
    {{ Γ ⊢ ℕ : A }} ->
    {{ Γ ⊢ Type@0 ⊆ A }}.
Proof.
  intros * H.
  assert (forall i, 0 <= i) by lia.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_nat_inversion : mcltt.

Lemma wf_pi_inversion : forall {Γ A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists i, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }} /\ {{ Γ ⊢ Type@i ⊆ C }}.
Proof.
  intros * H.
  dependent induction H; assert {{ ⊢ Γ }} by mauto 3; try solve [eexists; mauto 4];
    specialize (IHwf_exp _ _ eq_refl); destruct_conjs; eexists; repeat split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcltt.

Corollary wf_pi_inversion' : forall {Γ A B i},
    {{ Γ ⊢ Π A B : Type@i }} ->
    {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}.
Proof with mautosolve 4.
  intros * [j [? []]]%wf_pi_inversion.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@j[Wk] }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j[Wk] ⊆ Type@i[Wk] }} by mauto 4.
  assert {{ Γ, A ⊢ Type@i[Wk] ⊆ Type@i }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@i }}...
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mcltt.
