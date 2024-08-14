From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export System.
Import Syntax_Notations.

Lemma wf_typ_inversion : forall {Γ i A},
    {{ Γ ⊢ Type@i : A }} ->
    {{ Γ ⊢ Type@(S i) ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H...
Qed.

#[export]
Hint Resolve wf_typ_inversion : mcltt.

Lemma wf_nat_inversion : forall Γ A,
    {{ Γ ⊢ ℕ : A }} ->
    {{ Γ ⊢ Type@0 ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  assert (forall i, 0 <= i) by lia.
  dependent induction H...
Qed.

#[export]
Hint Resolve wf_nat_inversion : mcltt.

Lemma wf_pi_inversion : forall {Γ A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists i, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }} /\ {{ Γ ⊢ Type@i ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    assert {{ ⊢ Γ }} by mauto 3;
    eexists; split...
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcltt.

Corollary wf_pi_inversion' : forall {Γ A B i},
    {{ Γ ⊢ Π A B : Type@i }} ->
    {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}.
Proof with mautosolve 4.
  intros * [j [? []]]%wf_pi_inversion.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@j[Wk] }} by (econstructor; mauto 4).
  assert {{ Γ, A ⊢ Type@j[Wk] ⊆ Type@i[Wk] }} by mauto 4.
  assert {{ Γ, A ⊢ Type@i[Wk] ⊆ Type@i }} by (econstructor; mauto 4).
  enough {{ Γ, A ⊢ Type@j ⊆ Type@i }}...
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mcltt.
