From Coq Require Import Setoid Nat.
From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Syntactic Require Export CoreInversions.
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

Corollary invert_sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  autorewrite with mcltt in *; eassumption.
Qed.

#[export]
Hint Resolve invert_sub_id_typ : mcltt.

Lemma invert_compose_id : forall {Γ σ Δ},
    {{ Γ ⊢s σ ∘ Id : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_compose_id : mcltt.

Add Parametric Morphism i Γ Δ : a_sub
    with signature wf_exp_eq Δ {{{ Type@i }}} ==> wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Type@i }}} as sub_typ_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

Add Parametric Morphism Γ1 Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

Lemma wf_ctx_sub_length : forall Γ Δ,
    {{ ⊢ Γ ⊆ Δ }} ->
    length Γ = length Δ.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

Lemma app_ctx_lookup : forall Δ T Γ n,
    length Δ = n ->
    {{ #n : ~(iter (S n) (fun T => {{{T [ Wk ]}}}) T) ∈ ~(Δ ++ T :: Γ) }}.
Proof.
  induction Δ; intros; simpl in *; subst; mauto.
Qed.

Lemma ctx_lookup_functional : forall n T Γ,
    {{ #n : T ∈ Γ }} ->
    forall T',
      {{ #n : T' ∈ Γ }} ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  erewrite IHctx_lookup; eauto.
Qed.

Lemma app_ctx_vlookup : forall Δ T Γ n,
    {{ ⊢ ~(Δ ++ T :: Γ) }} ->
    length Δ = n ->
    {{ ~(Δ ++ T :: Γ) ⊢ #n : ~(iter (S n) (fun T => {{{T [ Wk ]}}}) T) }}.
Proof.
  intros. econstructor; auto using app_ctx_lookup.
Qed.

Lemma sub_q_eq : forall Δ A i Γ σ σ',
                   {{ Δ ⊢ A : Type@i }} ->
                   {{ Γ ⊢s σ ≈ σ' : Δ }} ->
                   {{ Γ, A[σ] ⊢s q σ ≈ q σ' : Δ, A }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - rewrite <- @exp_eq_sub_compose_typ; mauto 4.
Qed.
#[export]
 Hint Resolve sub_q_eq : mcltt.

Lemma wf_subtyp_subst_eq : forall Δ A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Δ }} ->
      {{ Γ ⊢ A [σ] ⊆ B[σ'] }}.
Proof.
  induction 1; intros * Hσσ'; gen_presup Hσσ'.
  - eapply wf_subtyp_refl'.
    eapply wf_exp_eq_conv; mauto 4.
  - etransitivity; mauto 4.
  - autorewrite with mcltt.
    mauto 2.
  - autorewrite with mcltt.
    eapply wf_subtyp_pi'; mauto.
Qed.

Lemma wf_subtyp_subst : forall Δ A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A [σ] ⊆ B[σ] }}.
Proof.
  intros; mauto 2 using wf_subtyp_subst_eq.
Qed.
#[export]
Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcltt.

Lemma exp_typ_sub_lhs : forall {Γ σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Type@i[σ] : Type@(S i) }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_typ_sub_lhs : mcltt.

Lemma exp_nat_sub_lhs : forall {Γ σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] : Type@i }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_nat_sub_lhs : mcltt.

Lemma exp_zero_sub_lhs : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ zero[σ] : ℕ }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_zero_sub_lhs : mcltt.

Lemma exp_succ_sub_lhs : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ (succ M)[σ] : ℕ }}.
Proof.
  intros; mauto 3.
Qed.
#[export]
Hint Resolve exp_succ_sub_lhs : mcltt.

Lemma exp_succ_sub_rhs : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ succ (M[σ]) : ℕ }}.
Proof.
  intros; mauto 3.
Qed.
#[export]
Hint Resolve exp_succ_sub_rhs : mcltt.

Lemma sub_decompose_q : forall Γ S i σ Δ Δ' τ t,
  {{Γ ⊢ S : Type@i}} ->
  {{Δ ⊢s σ : Γ}} ->
  {{Δ' ⊢s τ : Δ}} ->
  {{Δ' ⊢ t : S [ σ ] [ τ ]}} ->
  {{Δ' ⊢s q σ ∘ (τ ,, t) ≈ σ ∘ τ ,, t : Γ, S}}.
Proof.
  intros. gen_presups.
  simpl. autorewrite with mcltt.
  symmetry.
  rewrite wf_sub_eq_extend_compose; mauto 3;
    [| mauto
    | rewrite <- @exp_eq_sub_compose_typ; mauto 4].
  eapply wf_sub_eq_extend_cong; eauto.
  - rewrite wf_sub_eq_compose_assoc; mauto 3; mauto 4.
    rewrite wf_sub_eq_p_extend; eauto; mauto 4.
  - rewrite <- @exp_eq_sub_compose_typ; mauto 4.
Qed.

#[local]
Hint Rewrite -> @sub_decompose_q using mauto 4 : mcltt.

Lemma sub_decompose_q_typ : forall Γ S T i σ Δ Δ' τ t,
  {{Γ, S ⊢ T : Type@i}} ->
  {{Δ ⊢s σ : Γ}} ->
  {{Δ' ⊢s τ : Δ}} ->
  {{Δ' ⊢ t : S [ σ ] [ τ ]}} ->
  {{Δ' ⊢ T [ σ ∘ τ ,, t ] ≈ T [ q σ ] [ τ ,, t ] : Type@i}}.
Proof.
  intros. gen_presups.
  autorewrite with mcltt.
  eapply exp_eq_sub_cong_typ2'; [mauto 2 | econstructor; mauto 4 |].
  eapply sub_eq_refl; econstructor; mauto 3.
Qed.

Lemma sub_eq_p_q_sigma_compose_tau_extend : forall {Δ' τ Δ M A i σ Γ},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ' ⊢s τ : Δ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ' ⊢ M : A[σ][τ] }} ->
    {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 2.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ] }} by mauto 3.
  transitivity {{{ Wk∘((σ∘τ),,M) }}}; [| autorewrite with mcltt; mauto 3].
  eapply wf_sub_eq_compose_cong; [| mauto 2].
  autorewrite with mcltt; econstructor; mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Type@i }} as -> by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcltt.
#[export]
Hint Rewrite -> @sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcltt.

Lemma exp_eq_natrec_cong_rhs_typ : forall {Γ M M' A A' i},
    {{ Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ A[Id,,M] ≈ A'[Id,,M'] : Type@i }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ ℕ[Id] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Γ ⊢ M ≈ M' : ℕ[Id] }} by mauto 3.
  assert {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, ℕ }} as -> by mauto 3.
  mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_natrec_cong_rhs_typ : mcltt.

(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_lhs_typ_gen : forall {Γ σ Δ M A B i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert (exists j, {{ Δ ⊢ A : Type@j }}) as [] by mauto 3.
  assert {{ Δ ⊢s Id,,M : Δ, A }} by mauto 3.
  autorewrite with mcltt.
  assert {{ Γ ⊢ M[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M[σ] ≈ (Id,,M)∘σ : Δ, A }} as -> by mauto 3.
  mauto 4.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen : mcltt.

(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_rhs_typ : forall {Γ σ Δ M A B i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Type@i }}.
Proof.
  intros.
  assert (exists j, {{ Δ ⊢ A : Type@j }}) as [] by mauto 3.
  autorewrite with mcltt.
  assert {{ Γ ⊢s σ∘Id ≈ σ : Δ }} by mauto 3.
  assert {{ Γ ⊢s σ,,M ≈ (σ∘Id),,M : Δ, A }} as <-; mauto 4.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ : mcltt.

Lemma exp_eq_sub_cong_typ2 : forall {Δ Γ A σ τ i},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  gen_presups.
  mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_sub_cong_typ2 : mcltt.
#[export]
Remove Hints exp_eq_sub_cong_typ2' : mcltt.

Lemma exp_eq_nat_beta_succ_rhs_typ_gen : forall {Γ σ Δ i A M N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ N : A[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk,,succ #1][σ,,M,,N] ≈ A[σ,,succ M] : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢s Wk : Δ, ℕ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk : Δ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s σ,,M : Δ, ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M,,N : Δ, ℕ, A }} by mauto 3.
  assert {{ Γ ⊢s σ,,M,,N : Δ, ℕ, A }} by mauto 3.
  autorewrite with mcltt.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ ((Wk∘Wk)∘(σ,,M,,N)),,(succ #1)[σ,,M,,N] : Δ, ℕ }} as -> by mauto 4.
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(Wk∘(σ,,M,,N)) : Δ }} by mauto 3.
  assert {{ Γ ⊢s Wk∘(σ,,M,,N) ≈ σ,,M : Δ, ℕ }} by (autorewrite with mcltt; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(σ,,M) : Δ }} by (unshelve bulky_rewrite; constructor).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Δ }} by bulky_rewrite.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#1[σ,,M,,N]) : ℕ }} by mauto 3.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#0[σ,,M]) : ℕ }} by (bulky_rewrite; mauto 4).
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ M : ℕ }} by (bulky_rewrite; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N] ≈ σ,,succ M : Δ, ℕ }} by mauto 3.
  mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_nat_beta_succ_rhs_typ_gen : mcltt.

Lemma exp_pi_sub_lhs : forall {Γ σ Δ A B i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ (Π A B)[σ] : Type@i }}.
Proof.
  intros.
  mauto 4.
Qed.
#[export]
Hint Resolve exp_pi_sub_lhs : mcltt.

Lemma exp_pi_sub_rhs : forall {Γ σ Δ A B i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ Π A[σ] B[q σ] : Type@i }}.
Proof.
  intros.
  econstructor; mauto 3.
Qed.
#[export]
Hint Resolve exp_pi_sub_rhs : mcltt.

Lemma exp_pi_eta_rhs_body : forall {Γ A B M},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ, A ⊢ M[Wk] #0 : B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 2.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ M[Wk] : (Π A B)[Wk] }} by mauto 3.
  assert {{ Γ, A ⊢ Π A[Wk] B[q Wk] ≈ (Π A B)[Wk] : Type@i }} by (autorewrite with mcltt; mauto 3).
  assert {{ Γ, A ⊢ M[Wk] : Π A[Wk] B[q Wk] }} by mauto 3.
  econstructor; [econstructor; revgoals; mauto 3 | mauto 3 |].
  eapply wf_subtyp_refl'.
  autorewrite with mcltt.
  - transitivity {{{ B[Id] }}}; [| mauto 3].
    eapply exp_eq_sub_cong_typ2; mauto 4.
    transitivity {{{ Wk,,#0 }}}; [| mauto 3].
    econstructor; mauto 3.
    autorewrite with mcltt.
    mauto 3.
  - econstructor; mauto 3.
    autorewrite with mcltt.
    mauto 3.
Qed.
#[export]
Hint Resolve exp_pi_eta_rhs_body : mcltt.

(** This works for both var_0 and var_S cases *)
Lemma exp_eq_var_sub_rhs_typ_gen : forall {Γ σ Δ i A M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Type@i }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Δ, A }} by mauto 3.
  autorewrite with mcltt.
  mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_var_sub_rhs_typ_gen : mcltt.

Lemma exp_sub_decompose_double_q_with_id_double_extend : forall Γ A B C σ Δ M N L,
  {{ Γ, B, C ⊢ M : A }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢ N : B[σ] }} ->
  {{ Δ ⊢ L : C[σ,,N] }} ->
  {{ Δ ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert (exists i, {{ Γ ⊢ B : Type@i }}) as [] by mauto 3.
  assert {{ Δ, B[σ] ⊢s q σ : Γ, B }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, B[σ] }} by mauto 3.
  assert {{ Δ ⊢ L : C[q σ][Id,,N] }} by (rewrite -> @exp_eq_elim_sub_rhs_typ; mauto 3).
  assert {{ Δ ⊢ L : C[q σ∘(Id,,N)] }} by mauto 4.
  assert {{ Δ ⊢s Id,,N,,L : Δ, B[σ], C[q σ] }} by mauto 3.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  exvar nat ltac:(fun i => assert {{ Δ ⊢ C[q σ][Id,,N] ≈ C[σ,,N] : Type@i }} by mauto 3).
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B, C }} by (eapply sub_decompose_q; mauto 3).
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by (bulky_rewrite; mauto 3).
  exvar nat ltac:(fun i => assert {{ Δ ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] : Type@i }} by mauto 3).
  exvar nat ltac:(fun i => assert {{ Δ ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] : Type@i }} as <- by mauto 3).
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto 4.
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 3).
  symmetry; mauto 3.
Qed.

#[export]
Hint Resolve exp_sub_decompose_double_q_with_id_double_extend : mcltt.

Lemma sub_eq_q_compose : forall {Γ A i σ Δ τ Δ'},
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', A[σ∘τ] ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A }}.
Proof.
  intros.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Type@i }} by mauto 3.
  assert {{ ⊢ Δ', A[σ][τ] }} by mauto 4.
  assert {{ ⊢ Δ', A[σ∘τ] ≈ Δ', A[σ][τ] }} as -> by mauto.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ ⊢ Δ, A[σ] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  transitivity {{{ ((σ∘Wk)∘q τ),,#0[q τ] }}}; [econstructor; mauto 3 |].
  symmetry; econstructor; mauto 3; symmetry.
  - transitivity {{{ σ∘(Wk∘q τ) }}}; [mauto 4 |].
    assert {{ Δ' ⊢ A[σ][τ] : Type@i }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢s Wk : Δ' }} by mauto 3.
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] : Type@i }} by mauto 4.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] : Type@i }} by mauto.
    bulky_rewrite.
    econstructor; mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] : Type@i }} as <- by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] : Type@i }} as -> by mauto.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] : Type@i }} as -> by mauto 3.
    mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_q_compose : mcltt.
#[export]
Hint Rewrite -> @sub_eq_q_compose using mauto 4 : mcltt.

Lemma sub_eq_q_compose_nat : forall {Γ σ Δ τ Δ'},
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }}.
Proof.
  intros.
  assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ' ⊢ ℕ[σ∘τ] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ ⊢ Δ', ℕ[σ∘τ] ≈ Δ', ℕ }} as <- by mauto 3.
  mautosolve 2.
Qed.

#[export]
Hint Resolve sub_eq_q_compose_nat : mcltt.
#[export]
Hint Rewrite -> @sub_eq_q_compose_nat using mauto 4 : mcltt.

Lemma exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 : forall {Δ σ Γ i A},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] : Type@i }}.
Proof.
  intros.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[q σ∘(Wk∘Wk,,succ #1)] : Type@i }} as -> by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘q (q σ)] : Type@i }} as -> by mauto 3.
  rewrite -> @sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1; mauto 2.
  eapply exp_eq_refl.
  eapply exp_sub_typ; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 : mcltt.
