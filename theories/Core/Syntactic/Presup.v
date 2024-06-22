From Mcltt Require Import Base CtxEq LibTactics.
From Mcltt Require Export System.
Import Syntax_Notations.

#[local]
Ltac gen_presup_ctx H :=
  match type of H with
  | {{ ⊢ ~?Γ ≈ ~?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_ctx_eq H as [HΓ HΔ]
  | {{ ⊢ ~?Γ ⊆ ~?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_ctx_sub H as [HΓ HΔ]
  | {{ ~?Γ ⊢s ~?σ : ~?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_ctx H as [HΓ HΔ]
  end.

#[local]
Ltac gen_presup_IH presup_exp presup_exp_eq presup_sub_eq presup_subtyping H :=
  match type of H with
  | {{ ~?Γ ⊢ ~?M : ~?A }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HAi := fresh "HAi" in
      pose proof presup_exp _ _ _ H as [HΓ [i HAi]]
  | {{ ~?Γ ⊢ ~?M ≈ ~?N : ~?A }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HAi := fresh "HAi" in
      pose proof presup_exp_eq _ _ _ _ H as [HΓ [HM [HN [i HAi]]]]
  | {{ ~?Γ ⊢s ~?σ ≈ ~?τ : ~?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | {{ ~?Γ ⊢ ~?M ⊆ ~?N }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      pose proof presup_subtyping _ _ _ H as [HΓ [i [HM HN]]]
  | _ => gen_presup_ctx H
  end.

Lemma presup_exp : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_exp_eq : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_sub_eq : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_subtyping : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ M : Type@i }} /\ {{ Γ ⊢ M' : Type@i }}.
Proof with mautosolve 4.
  2: set (WkWksucc := {{{ Wk∘Wk ,, succ #1 }}}).
  all: inversion_clear 1; (on_all_hyp: gen_presup_IH presup_exp presup_exp_eq presup_sub_eq presup_subtyping);
    clear presup_exp presup_exp_eq presup_sub_eq presup_subtyping;
    repeat split; mauto 4;
    try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B');
    try (rename N into L); try (rename N' into L');
    try (rename M0 into N); try (rename MZ into NZ); try (rename MS into NS);
    try (rename M'0 into N'); try (rename MZ' into NZ'); try (rename MS' into NS');
    try (rename M' into N').
  (* presup_exp cases *)
  - eexists.
    assert {{ Γ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Γ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right...

  (* presup_exp_eq cases *)
  - assert {{ Γ ⊢s Id ,, N ≈ Id ,, N' : Γ, ℕ }} by mauto 4.
    assert {{ Γ ⊢ B[Id ,, N] ≈ B[Id ,, N'] : Type@i }} by mauto.
    assert {{ Γ ⊢ B[Id ,, N] ≈ B'[Id ,, N'] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Id ,, zero] ≈ B'[Id ,, zero] : Type@i }} by mauto.
    assert {{ Γ ⊢ NZ' : B'[Id ,, zero] }} by mauto.
    assert {{ Γ, ℕ, B ⊢ NS' : B'[WkWksucc] }} by mauto 4.
    assert {{ Γ, ℕ, B' ⊢ NS' : B'[WkWksucc] }} by mauto 4.
    enough {{ Γ ⊢ rec N' return B' | zero -> NZ' | succ -> NS' end : B'[Id ,, N'] }}...

  - assert {{ Γ ⊢ B[(Id,,N)][σ] ≈ B[(Id,,N)∘σ] : Type@i }} by mauto 4.
    assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 4.
    enough {{ Γ ⊢ B[(Id,,N)][σ] ≈ B[σ,,N[σ]] : Type@i }}...

  - assert {{ Γ ⊢s Id,,N[σ] : Γ, ℕ }} by mauto.
    assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
    assert {{ Γ, ℕ ⊢ B[q σ] : Type@i }} by mauto.
    assert {{ Γ ⊢ B[q σ][(Id,,N[σ])] ≈ B[q σ∘(Id,,N[σ])] : Type@i }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Type@i }} by mauto.
    assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Type@i }} by mauto.
    assert {{ Γ ⊢ NZ[σ] : B[Id ,, zero][σ] }} by mauto.
    assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Type@0 }} by mauto.
    assert {{ Γ ⊢ zero : ℕ[σ] }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, zero) ≈ σ ,, zero : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢s σ ≈ Id∘σ : Δ }} by mauto.
    assert {{ Γ ⊢s σ ,, zero ≈ Id∘σ ,, zero[σ] : Δ, ℕ }} by mauto 4.
    assert {{ Γ ⊢s Id∘σ ,, zero[σ] ≈ (Id ,, zero)∘σ : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢s Id ,, zero : Γ, ℕ }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, zero) ≈ (Id ,, zero)∘σ : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢ B[q σ∘(Id ,, zero)] ≈ B[(Id ,, zero)∘σ] : Type@i }} by mauto.
    assert {{ Γ ⊢ B[q σ][Id ,, zero] ≈ B[Id ,, zero][σ] : Type@i }} by mauto.
    assert {{ Γ ⊢ NZ[σ] : B[q σ][Id ,, zero] }} by mauto.
    set (Γ' := {{{ Γ, ℕ, B[q σ] }}}).
    assert {{ Γ' ⊢s q (q σ) : Δ, ℕ, B }} by mauto 4.
    assert {{ Γ' ⊢s q σ∘WkWksucc ≈ WkWksucc∘q (q σ) : Δ, ℕ }} by mauto.
    assert {{ Γ' ⊢s WkWksucc : Γ, ℕ }} by mauto.
    assert {{ Γ' ⊢ B[q σ][WkWksucc] ≈ B[WkWksucc][q (q σ)] : Type@i }} by mauto.
    assert {{ Γ' ⊢ NS[q (q σ)] : B[q σ][WkWksucc] }}...

  - eexists...

  - set (recN := {{{ rec N return B | zero -> NZ | succ -> NS end }}}).
    set (IdNrecN := {{{ Id ,, N ,, recN }}}).
    assert {{ Γ ⊢ recN : B[Id ,, N] }} by mauto.
    assert {{ Γ ⊢s WkWksucc∘IdNrecN ≈ (Wk∘Wk)∘IdNrecN ,, (succ #1)[IdNrecN] : Γ, ℕ }}
      by (eapply sub_eq_extend_compose_nat; mauto 4).
    assert {{ Γ ⊢s IdNrecN : Γ, ℕ, B }} by mauto.
    assert {{ Γ, ℕ, B ⊢s Wk∘Wk : Γ }} by mauto 4.
    assert {{ Γ ⊢s (Wk∘Wk)∘IdNrecN : Γ }} by mauto 4.
    assert {{ Γ ⊢s (Wk∘Wk)∘IdNrecN ≈ Wk∘(Wk∘IdNrecN) : Γ }} by mauto 4.
    assert {{ Γ ⊢s Id,,N : Γ, ℕ }} by mauto 4.
    assert {{ Γ ⊢s Wk∘(Wk∘IdNrecN) ≈ Wk∘(Id ,, N) : Γ }} by mauto 4.
    assert {{ Γ ⊢s (Wk∘Wk)∘IdNrecN ≈ Id : Γ }} by mauto 4.
    assert {{ Γ ⊢ #1[IdNrecN] ≈ #0[Id ,, N] : ℕ }} by mauto.
    assert {{ Γ ⊢ #1[IdNrecN] ≈ N : ℕ }} by mauto 4.
    assert {{ Γ ⊢ succ #1[IdNrecN] ≈ succ N : ℕ }} by mauto.
    assert {{ Γ ⊢ (succ #1)[IdNrecN] ≈ succ N : ℕ }} by mauto 4.
    assert {{ Γ ⊢s (Wk∘Wk)∘IdNrecN ,, (succ #1)[IdNrecN] ≈ Id ,, succ N : Γ , ℕ }} by mauto.
    assert {{ Γ ⊢s WkWksucc∘IdNrecN : Γ, ℕ }} by mauto.
    assert {{ Γ ⊢s Id,,succ N : Γ, ℕ }} by mauto.
    assert {{ Γ ⊢s WkWksucc∘IdNrecN ≈ Id ,, succ N : Γ , ℕ }} by mauto.
    assert {{ Γ ⊢ B[WkWksucc∘IdNrecN] ≈ B[Id,,succ N] : Type@i }} by mauto 4.
    enough {{ Γ ⊢ B[WkWksucc][IdNrecN] ≈ B[Id,,succ N] : Type@i }}...

  - eexists...

  - mauto.

  - mauto.

  - assert {{ Γ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Γ ⊢ B ≈ B' : Type@(max i i0) }} by mauto using lift_exp_eq_max_left.
    assert {{ Γ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right.
    assert {{ Γ ⊢ Π B C ≈ Π B' C : Type@(max i i0) }} by mauto.
    assert {{ Γ, B' ⊢ N' : C }} by mauto 4.
    enough {{ Γ ⊢ λ B' N' : Π B' C }}...

  - assert {{ Γ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Γ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right...

  - assert {{ Δ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Δ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right.
    assert {{ Γ ⊢ B[σ] : Type@(max i i0) }} by mauto.
    assert {{ Γ, B[σ] ⊢ C[q σ] : Type@(max i i0) }} by mauto 4.
    assert {{ Γ ⊢ Π B[σ] C[q σ] : Type@(max i i0) }} by mauto.
    assert {{ Γ ⊢ Π B[σ] C[q σ] ≈ Π B[σ] C[q σ] : Type@(max i i0) }} by mauto.
    assert {{ Γ, B[σ] ⊢ N[q σ] : C[q σ] }} by mauto 4.
    enough {{ Γ ⊢ λ B[σ] N[q σ] : Π B[σ] C[q σ] }}...

  - assert {{ Δ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Δ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right.
    enough {{ Δ ⊢ Π B C : Type@(max i i0) }}...

  - assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto.
    assert {{ Γ ⊢ B[Id] ≈ B : Type@i }} by mauto.
    assert {{ Γ ⊢ L ≈ L' : B[Id] }} by mauto.
    assert {{ Γ ⊢s Id ,, L ≈ Id ,, L' : Γ, B }} by mauto.
    enough {{ Γ ⊢ C[Id ,, L] ≈ C[Id ,, L'] : Type@i }}...

  - assert {{ Γ ⊢ N[σ] : Π B[σ] C[q σ] }} by mauto 4.
    assert {{ Δ ⊢ L : B[Id] }} by mauto 4.
    assert {{ Γ ⊢s (Id ,, L)∘σ ≈ Id∘σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Γ ⊢s (Id ,, L)∘σ ≈ σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Δ ⊢s Id ,, L : Δ, B }} by mauto.
    assert {{ Γ ⊢s (Id ,, L)∘σ : Δ, B }} by mauto.
    assert {{ Γ ⊢ C[(Id ,, L)∘σ] ≈ C[σ ,, L[σ]] : Type@i }} by mauto.
    enough {{ Γ ⊢ C[Id ,, L][σ] ≈ C[σ ,, L[σ]] : Type@i }}...

  - assert {{ Γ ⊢ B[σ] : Type@i }} by mauto.
    assert {{ Γ, B[σ] ⊢ C[q σ] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ N[σ] : Π B[σ] C[q σ] }} by mauto 4.
    assert {{ Γ ⊢ L[σ] : B[σ] }} by mauto.
    assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, L[σ]) ≈ σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Γ ⊢s Id ,, L[σ] : Γ, B[σ] }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, L[σ]) : Δ, B }} by mauto.
    assert {{ Γ ⊢ C[q σ∘(Id ,, L[σ])] ≈ C[σ ,, L[σ]] : Type@i }} by mauto 4.
    enough {{ Γ ⊢ C[q σ][(Id ,, L[σ])] ≈ C[σ ,, L[σ]] : Type@i }}...

  - eexists...

  - set (Id0 := {{{ Id ,, #0 }}}).
    assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto.
    assert {{ Γ, B, B[Wk] ⊢ C[q Wk] : Type@i }} by mauto.
    assert {{ Γ, B ⊢ M[Wk] : (Π B C)[Wk] }} by mauto.
    assert {{ Γ, B ⊢ M[Wk] : Π B[Wk] C[q Wk] }} by mauto.
    assert {{ Γ, B ⊢ #0 : B[Wk] }} by mauto.
    assert {{ Γ, B ⊢s Id0 : Γ, B, B[Wk] }} by mauto.
    assert {{ Γ, B ⊢ M[Wk] #0 : C[q Wk][Id0] }} by mauto.
    assert {{ Γ, B, B[Wk] ⊢s q Wk : Γ, B }} by mauto 4.
    assert {{ Γ, B ⊢ M[Wk] #0 : C[q Wk ∘ Id0] }} by mauto 4.
    assert {{ Γ, B ⊢ B[Wk][Id] ≈ B[Wk] : Type@i }} by mauto.
    assert {{ Γ, B ⊢ #0 : B[Wk][Id] }} by mauto 3.
    assert {{ Γ, B ⊢s Id0 : Γ, B, B[Wk] }} by mauto.
    assert {{ Γ, B ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, B, B[Wk] ⊢s Wk∘Wk : Γ }} by mauto 4.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 : Γ }} by mauto 4.
    assert {{ Γ, B, B[Wk] ⊢s Wk : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s Id ≈ Wk∘Id0 : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s Wk∘Id ≈ Wk∘(Wk∘Id0) : Γ }} by mauto.
    assert {{ Γ, B ⊢s Wk∘Id ≈ (Wk∘Wk)∘Id0 : Γ }} by mauto 4.
    assert {{ Γ, B, B[Wk] ⊢ #0 : B[Wk][Wk] }} by mauto 4.
    assert {{ Γ, B, B[Wk] ⊢ #0 : B[Wk∘Wk] }} by mauto 3.
    assert {{ Γ, B ⊢s q Wk ∘ Id0 ≈ (Wk∘Wk)∘Id0 ,, #0[Id0] : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ≈ Wk∘(Wk∘Id0) : Γ }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ≈ Wk∘Id : Γ }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0 : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0 ≈ #0[Id] : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[Wk∘Id] }} by mauto 4.
    assert {{ Γ, B ⊢ B[Wk∘Id] ≈ B[(Wk∘Wk)∘Id0] : Type@i }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[(Wk∘Wk)∘Id0] }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ,, #0[Id0] ≈ Wk∘Id ,, #0[Id] : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s Wk∘Id ,, #0[Id] ≈ Id : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s q Wk ∘ Id0 ≈ Id : Γ, B }} by mauto.
    assert {{ Γ, B ⊢ C[q Wk ∘ Id0] ≈ C[Id] : Type@i }} by mauto 4.
    enough {{ Γ, B ⊢ M[Wk] #0 : C }}...

  - assert {{ Γ ⊢s Wk∘(σ ,, N') ≈ σ : Δ }} by mauto.
    assert {{ Γ ⊢ B[Wk∘(σ ,, N')] ≈ B[σ] : Type@i }} by mauto.
    assert {{ ⊢ Δ, B }} by mauto.
    assert {{ Δ, B ⊢s Wk : Δ }} by mauto.
    assert {{ Γ ⊢s σ ,, N' : Δ, B }} by mauto.
    assert {{ Γ ⊢ B[Wk][σ ,, N'] ≈ B[σ] : Type@i }} by mauto 3.
    enough {{ Γ ⊢ #0[σ ,, N'] : B[Wk][σ ,, N'] }}...

  - assert (exists i, {{ Δ ⊢ C : Type@i }}) as [i'] by mauto 3.
    assert {{ Γ ⊢s Wk∘(σ ,, N) ≈ σ : Δ }} by mauto.
    assert {{ Γ ⊢ C[Wk∘(σ ,, N)] ≈ C[σ] : Type@i' }} by mauto.
    assert {{ Δ, B ⊢s Wk : Δ }} by mauto.
    assert {{ Γ ⊢s σ ,, N : Δ, B }} by mauto.
    assert {{ Γ ⊢ C[Wk][σ ,, N] ≈ C[σ] : Type@i' }} by mauto 3.
    assert {{ Δ, B ⊢ #(S x) : C[Wk] }} by mauto 4.
    enough {{ Γ ⊢ #(S x)[σ ,, N] : C[Wk][σ ,, N] }}...

  - assert (exists i, {{ Δ ⊢ C : Type@i }}) as []...

  (* presup_sub_eq cases *)
  - econstructor...

  - assert {{ Γ ⊢ B[σ] ≈ B[σ'] : Type@i }}...

  - assert {{ Γ ⊢ N'[Id] : A[Id] }}...

  - assert {{ Γ ⊢ N[σ][τ] : B[σ][τ] }}...

  - econstructor...

  - assert {{ ⊢ Δ, A }}...

  - assert (exists i, {{ Γ0 ⊢ A : Type@i }}) as [] by mauto.
    assert {{ Γ ⊢ #0[σ] : A[Wk][σ] }} by mauto.
    enough {{ Γ ⊢ #0[σ] : A[Wk∘σ] }}...

    (* presup_subtyping cases *)
  - exists (max i i0); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - exists (max (S i) (S j)); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - mauto.
Qed.

#[export]
Hint Resolve presup_exp presup_exp_eq presup_sub_eq presup_subtyping : mcltt.

Ltac gen_presup H := gen_presup_IH @presup_exp @presup_exp_eq @presup_sub_eq @presup_subtyping H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; clear_dups.
