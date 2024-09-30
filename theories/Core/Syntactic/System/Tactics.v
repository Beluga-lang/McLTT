From Mcltt Require Import Base LibTactics.
From Mcltt Require Export System.Definitions System.Lemmas.
Import Syntax_Notations.

#[global]
Ltac pi_univ_level_tac :=
  match goal with
  | |- {{ ~_ ⊢s ~_ : ~_ }} => mauto 4
  | H : {{ ~?Δ ⊢ ~?A : Type@?j }} |- {{ ~?Δ , ~?A ⊢ ~?B : Type@?i }} =>
      eapply lift_exp_max_right; mauto 4
  | |- {{ ~?Δ ⊢ ~?A : Type@?j }} =>
      eapply lift_exp_max_left; mauto 4
  end.

#[export]
Hint Rewrite -> wf_exp_eq_pi_sub using pi_univ_level_tac : mcltt.

#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ⊢ ~_ , ~_ }} =>
      let H' := fresh "H" in
      pose proof H as H';
      progressive_invert H'
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

Lemma trans_exp_eq_natrec_cong : forall {Γ i A A' M M' MZ MZ' MS MS' N},
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
  {{ Γ ⊢ M ≈ M' : ℕ }} ->
  {{ Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end ≈ N : A'[Id,,M'] }} ->
  {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ N : A[Id,,M] }}.
Admitted.

Lemma trans_exp_eq_natrec_sub : forall {Γ σ Δ i A M MZ MS N},
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ MZ : A[Id,,zero] }} ->
  {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
  {{ Δ ⊢ M : ℕ }} ->
  {{ Γ ⊢ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ N : A[q σ][Id,,M[σ]] }} ->
  {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ N : A[Id,,M][σ] }}.
Admitted.

(* trans_exp_eq_nat_beta_zero is not useful as the type of RHS and LHS are the same. *)

Lemma trans_exp_eq_nat_beta_succ : forall {Γ i A M MZ MS N},
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
  {{ Γ ⊢ M : ℕ }} ->
  {{ Γ ⊢ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] ≈ N : A[Wk∘Wk,,succ #1][Id,,M,,rec M return A | zero -> MZ | succ -> MS end] }} ->
  {{ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ N : A[Id,,succ M] }}.
Admitted.

Lemma trans_exp_eq_fn_cong : forall {Γ i A A' B M M' N},
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ, A ⊢ M ≈ M' : B }} ->
  {{ Γ ⊢ λ A' M' ≈ N : Π A' B }} ->
  {{ Γ ⊢ λ A M ≈ N : Π A B }}.
Proof.
  intros.
  transitivity {{{ λ A' M' }}}; mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  symmetry; mauto 4.
Qed.

Lemma trans_exp_eq_fn_sub : forall {Γ σ Δ i A B M N},
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Δ, A ⊢ B : Type@i }} ->
  {{ Δ, A ⊢ M : B }} ->
  {{ Γ ⊢ λ A[σ] M[q σ] ≈ N : Π A[σ] B[q σ] }} ->
  {{ Γ ⊢ (λ A M)[σ] ≈ N : (Π A B)[σ] }}.
Proof.
  intros.
  transitivity {{{ λ A[σ] M[q σ] }}}; mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma beta_zero: forall {Γ i A M MZ MS},
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ zero : ℕ }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ#1] }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  intros.
  transitivity {{{ rec zero return A | zero -> MZ | succ -> MS end }}}.
  - symmetry.
    econstructor; mauto 3.
  - eapply wf_exp_eq_conv; [mauto 4 | mauto 4 |].
    eapply exp_eq_sub_cong_typ1; mauto 3.
Qed.

Ltac beta_normalize Γ M :=
  match M with
  | {{{ Type@?i }}} =>
    assert {{ Γ ⊢ Type@i ≈ Type@i : Type@(S i) }} by mauto 3
  | {{{ ℕ }}} =>
    assert {{ Γ ⊢ ℕ ≈ ℕ : Type@0 }} by mauto 3
  | {{{ zero }}} =>
    assert {{ Γ ⊢ zero ≈ zero : ℕ }} by mauto 3
  | {{{ succ ~?M' }}} =>
      eassert {{ Γ ⊢ succ M' ≈ succ ~_ : ℕ }}
        by (apply wf_exp_eq_succ_cong;
            beta_normalize Γ M; eassumption)
  | {{{ rec ~?M' return ~?A | zero -> ~?MZ | succ -> ~?MS end }}} =>
      let H := fresh "H" in
      eassert {{ Γ ⊢ M' ≈ ~_ : ℕ }} as H
          by (beta_normalize Γ M'; eassumption);
      idtac "fqefqwd";
      match type of H with
      | {{ Γ ⊢ ~_ ≈ zero : ℕ }} =>
          assert {{ Γ ⊢ rec M' return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}
            by (eapply beta_zero; mauto 3);
          idtac "fqefqwd";
          clear H
      end
  end.

Ltac beta_normalize_goal :=
  match goal with
  | |- {{ ~?Γ ⊢ ~?M ≈ ~?M' : ~?A }} =>
      beta_normalize Γ M
  end.

Goal {{ ⋅ ⊢ rec zero return ℕ | zero -> zero | succ -> zero end ≈ zero : ℕ }}.
Proof.
  assert {{ ⋅ ⊢ zero : ℕ[Id,,zero] }} by mauto 4.
  assert {{ ⋅, ℕ ⊢ ℕ : Type@0 }} by mauto 4.
  assert {{ ⋅, ℕ, ℕ ⊢s Wk∘Wk,,succ#1 : ⋅, ℕ }} by mauto 3.
  assert {{ ⋅, ℕ, ℕ ⊢ zero : ℕ[Wk∘Wk,,succ#1] }} by mauto 4.
  beta_normalize_goal.
  eassert {{ ⋅ ⊢ zero ≈ ~_ : ℕ }}.
  {
    beta_normalize ({{{ ⋅ }}} : ctx) {{{ zero }}}.
    eassumption.
  }
