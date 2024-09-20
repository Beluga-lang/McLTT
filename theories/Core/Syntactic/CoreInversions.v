From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics CtxSub.
From Mcltt.Core Require Export SystemOpt.
Import Syntax_Notations.

Corollary wf_zero_inversion : forall Γ A,
    {{ Γ ⊢ zero : A }} ->
    {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl)...
Qed.

#[export]
Hint Resolve wf_zero_inversion : mcltt.

Corollary wf_succ_inversion : forall Γ A M,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs...
Qed.

#[export]
Hint Resolve wf_succ_inversion : mcltt.

Lemma wf_natrec_inversion : forall Γ A M A' MZ MS,
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  pose (A0 := A).
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs;
    assert {{ Γ ⊢s Id : Γ }} by mauto 3;
    repeat split...
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mcltt.

Corollary wf_fn_inversion : forall {Γ A M C},
    {{ Γ ⊢ λ A M : C }} ->
    exists B, {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π A B ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    gen_presups;
    eexists; split...
Qed.

#[export]
Hint Resolve wf_fn_inversion : mcltt.

Lemma wf_app_inversion : forall {Γ M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B, {{ Γ ⊢ M : Π A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split...
Qed.

#[export]
Hint Resolve wf_app_inversion : mcltt.

Lemma wf_vlookup_inversion : forall {Γ x A},
    {{ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    [assert (exists i, {{ Γ ⊢ A : Type@i }}) as [] by mauto 4 |];
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs;
    eexists; split...
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mcltt.

Lemma wf_exp_sub_inversion : forall {Γ M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs;
    gen_presups;
    do 2 eexists; split...
Qed.

#[export]
Hint Resolve wf_exp_sub_inversion : mcltt.

(** We omit [wf_conv] and [wf_cumu] as they do not give useful inversions *)

Lemma wf_sub_id_inversion : forall Γ Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcltt.

Lemma wf_sub_weaken_inversion : forall {Γ Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion;
    repeat eexists; mauto.
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
    exists Δ' A', {{ ⊢ Δ', A' ⊆ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_sub _ _ eq_refl);
    destruct_conjs;
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcltt.
