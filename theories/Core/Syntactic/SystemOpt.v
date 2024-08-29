From Coq Require Import Setoid.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export CtxEq Presup System CoreTypeInversions.
Import Syntax_Notations.

Add Parametric Morphism i Γ : (wf_exp Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism i Γ : (wf_exp_eq Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism Γ i : (wf_subtyp Γ)
    with signature (wf_exp_eq Γ {{{Type@i}}}) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Γ j : (wf_subtyp Γ)
    with signature eq ==> (wf_exp_eq Γ {{{Type@j}}}) ==> iff as wf_subtyp_morphism_iff2.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 3.
Qed.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

Corollary wf_subtyp_refl' : forall Γ M M' i,
    {{ Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Γ ⊢ M ⊆ M' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mcltt.
#[export]
Remove Hints wf_subtyp_refl : mcltt.

Lemma wf_subtyp_pi' : forall Γ i A A' B B',
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Π A B ⊆ Π A' B' }}.
Proof.
  intros.
  gen_presups.
  assert {{ ⊢ Γ, A ≈ Γ, A' }} by mauto 3.
  assert {{ Γ ⊢ A : Type@(max i i0) }} by mauto 3 using lift_exp_max_left.
  assert {{ Γ ⊢ A' : Type@(max i i0) }} by mauto 3 using lift_exp_max_left.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i i0) }} by mauto 3 using lift_exp_eq_max_left.
  assert {{ Γ, A ⊢ B : Type@(max i i0) }} by mauto 4 using lift_exp_max_right.
  assert {{ Γ, A' ⊢ B' : Type@(max i i0) }} by mauto 4 using lift_exp_max_right.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mcltt.
#[export]
Remove Hints wf_subtyp_pi : mcltt.

Corollary wf_conv' : forall Γ M A i A',
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mcltt.
#[export]
Remove Hints wf_conv : mcltt.

Corollary wf_exp_eq_conv' : forall Γ M M' A A' i,
   {{ Γ ⊢ M ≈ M' : A }} ->
   {{ Γ ⊢ A ≈ A' : Type@i }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mcltt.
#[export]
Remove Hints wf_exp_eq_conv : mcltt.

Corollary wf_ctx_eq_extend' : forall {Γ Δ A A' i},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ ⊢ Γ , A ≈ Δ , A' }}.
Proof.
  intros.
  assert {{ Δ ⊢ A ≈ A' : Type@i }} by mauto.
  gen_presups.
  mautosolve 4.
Qed.

#[export]
Hint Resolve wf_ctx_eq_extend' : mcltt.
#[export]
Remove Hints wf_ctx_eq_extend : mcltt.

Corollary wf_nat' : forall {Γ i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ ℕ : Type@i }}.
Proof.
  intros.
  assert (0 <= i) by lia.
  mauto.
Qed.

#[export]
Hint Resolve wf_nat' : mcltt.
#[export]
Remove Hints wf_nat : mcltt.

Corollary wf_natrec' : forall {Γ A MZ MS M},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_natrec' : mcltt.
#[export]
Remove Hints wf_natrec : mcltt.

Corollary wf_pi_max : forall {Γ A i B j},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ , A ⊢ B : Type@j }} ->
    {{ Γ ⊢ Π A B : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left.
  assert {{ Γ, A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_pi_max : mcltt.

Corollary wf_fn' : forall {Γ A M B},
    {{ Γ , A ⊢ M : B }} ->
    {{ Γ ⊢ λ A M : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_fn' : mcltt.
#[export]
Remove Hints wf_fn : mcltt.

Corollary wf_app' : forall {Γ M N A B},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mcltt.
#[export]
Remove Hints wf_app : mcltt.

Lemma wf_exp_eq_typ_sub' : forall Γ σ Δ i j,
    {{ Γ ⊢s σ : Δ }} ->
    i < j ->
    {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@j }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_eq_typ_sub' : mcltt.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub' using solve [lia | mauto 3] : mcltt.

Corollary wf_exp_eq_nat_sub' : forall Γ σ Δ i,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@i }}.
Proof.
  intros.
  assert (0 <= i) by lia.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub' : mcltt.
#[export]
Remove Hints wf_exp_eq_nat_sub : mcltt.

#[export]
Hint Rewrite -> wf_exp_eq_nat_sub' using mautosolve 3 : mcltt.

Corollary wf_exp_eq_natrec_cong' : forall {Γ A A' i MZ MZ' MS MS' M M'},
    {{ Γ , ℕ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mcltt.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mcltt.

Corollary wf_exp_eq_natrec_sub' : forall {Γ σ Δ A MZ MS M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_sub' : mcltt.
#[export]
Remove Hints wf_exp_eq_natrec_sub : mcltt.

Corollary wf_exp_eq_nat_beta_zero' : forall {Γ A MZ MS},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mcltt.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mcltt.

Corollary wf_exp_eq_nat_beta_succ' : forall {Γ A MZ MS M},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mcltt.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mcltt.

Corollary wf_exp_eq_pi_sub_max : forall {Γ σ Δ A i B j},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ , A ⊢ B : Type@j }} ->
    {{ Γ ⊢ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Δ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left.
  assert {{ Δ , A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_sub_max : mcltt.

Corollary wf_exp_eq_pi_cong' : forall {Γ A A' B B' i},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ B ≈ B' : Type@i }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mcltt.
#[export]
Remove Hints wf_exp_eq_pi_cong : mcltt.

Corollary wf_exp_eq_pi_cong_max : forall {Γ A A' i B B' j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ B ≈ B' : Type@j }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ , A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mcltt.

Corollary wf_exp_eq_fn_cong' : forall {Γ A A' i B M M'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A ⊢ M ≈ M' : B }} ->
    {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcltt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mcltt.

Corollary wf_exp_eq_fn_sub' : forall {Γ σ Δ A M B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ , A ⊢ M : B }} ->
    {{ Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcltt.
#[export]
Remove Hints wf_exp_eq_fn_sub : mcltt.

Corollary wf_exp_eq_app_cong' : forall {Γ A B M M' N N'},
    {{ Γ ⊢ M ≈ M' : Π A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcltt.
#[export]
Remove Hints wf_exp_eq_app_cong : mcltt.

Corollary wf_exp_eq_app_sub' : forall {Γ σ Δ A B M N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Δ ⊢ A : Type@i }} /\ {{ Δ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcltt.
#[export]
Remove Hints wf_exp_eq_app_sub : mcltt.

Corollary wf_exp_eq_pi_beta' : forall {Γ A B M N},
    {{ Γ , A ⊢ M : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert {{ Γ ⊢ A : Type@i }} by (eapply lift_exp_max_left; mauto 3)).
  exvar nat ltac:(fun i => assert {{ Γ, A ⊢ B : Type@i }} by (eapply lift_exp_max_right; mauto 3)).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcltt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mcltt.

Corollary wf_exp_eq_pi_eta' : forall {Γ A B M},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_eta' : mcltt.
#[export]
Remove Hints wf_exp_eq_pi_eta : mcltt.


Lemma wf_subtyp_pi' : forall Γ A A' B B' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ , A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Π A B ⊆ Π A' B' }}.
Proof.
  intros. gen_presups.
  eapply wf_subtyp_pi with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
  eapply ctxeq_exp; [ | mauto 3 using lift_exp_max_right].
  mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mcltt.
#[export]
Remove Hints wf_subtyp_pi : mcltt.
