From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export SystemOpt.
Import Syntax_Notations.

Lemma wf_natrec_inversion : forall Γ A M A' MZ MS,
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  pose (A0 := A).
  dependent induction H;
    try (specialize (IHwf_exp _ _ _ _ eq_refl); destruct_conjs; repeat split; mautosolve 4).
  assert {{ Γ ⊢s Id : Γ }} by mauto 3.
  repeat split...
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mcltt.

Lemma wf_app_inversion : forall {Γ M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B, {{ Γ ⊢ M : Π A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try solve [do 2 eexists; repeat split; mauto 4];
    specialize (IHwf_exp _ _ eq_refl); destruct_conjs; do 2 eexists; repeat split...
Qed.

#[export]
Hint Resolve wf_app_inversion : mcltt.

Lemma wf_vlookup_inversion : forall {Γ x A},
    {{ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp _ eq_refl); destruct_conjs; eexists; split; mautosolve 4).
  assert (exists i, {{ Γ ⊢ A : Type@i }}) as []...
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mcltt.

Lemma wf_exp_sub_inversion : forall {Γ M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp _ _ eq_refl); destruct_conjs; do 2 eexists; repeat split; mautosolve 4).
  gen_presups.
  do 2 eexists.
  repeat split...
Qed.

#[export]
Hint Resolve wf_exp_sub_inversion : mcltt.

(* [wf_conv] and [wf_cumu] do not give useful inversions *)

Lemma wf_sub_id_inversion : forall Γ Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H; mauto.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcltt.

Lemma wf_sub_weaken_inversion : forall {Γ Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists A, {{ ⊢ Γ ≈ Δ, A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H; mauto.
  specialize (IHwf_sub eq_refl).
  destruct_conjs.
  eexists.
  gen_presups.
  etransitivity...
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcltt.

Lemma wf_sub_compose_inversion : forall {Γ1 σ1 σ2 Γ3},
    {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H; mauto.
  specialize (IHwf_sub _ _ eq_refl).
  destruct_conjs.
  eexists.
  repeat split...
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcltt.

Lemma wf_sub_extend_inversion : forall {Γ σ M Δ},
    {{ Γ ⊢s σ,,M : Δ }} ->
    exists Δ' A', {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A' }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcltt.
