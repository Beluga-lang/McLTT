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
Ltac gen_presup_IH presup_exp presup_exp_eq presup_sub_eq presup_subtyp H :=
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
      pose proof presup_subtyp _ _ _ H as [HΓ [i [HM HN]]]
  | _ => gen_presup_ctx H
  end.


Lemma presup_exp : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_exp_eq : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_sub_eq : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_subtyp : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ M : Type@i }} /\ {{ Γ ⊢ M' : Type@i }}.
Proof with mautosolve 4.
  2: set (WkWksucc := {{{ Wk∘Wk ,, succ #1 }}}).
  all: inversion_clear 1; (on_all_hyp: gen_presup_IH presup_exp presup_exp_eq presup_sub_eq presup_subtyp);
    clear presup_exp presup_exp_eq presup_sub_eq presup_subtyp;
    repeat split; mauto 4;
    try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B');
    try (rename N into L); try (rename N' into L');
    try (rename M0 into N); try (rename MZ into NZ); try (rename MS into NS);
    try (rename M'0 into N'); try (rename MZ' into NZ'); try (rename MS' into NS');
    try (rename M' into N').
  (** presup_exp cases *)
  - eexists.
    assert {{ Γ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Γ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right...

  - eexists.
    eapply exp_sub_typ; [eassumption |].
    assert {{ Γ ⊢s Id ,, M1 : Γ, B}} by mauto 4.
    assert {{ Γ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,M1] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,M1)]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, M1 ,, M2 : Γ, B , B[Wk]}}.
    {
      econstructor; mauto 3.
      eapply wf_conv; mauto 2.
    }
    assert {{ Γ ⊢ B[Wk][Wk][Id ,, M1 ,, M2] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id ,, M1 ,, M2)]}}};
        [| transitivity {{{B[Wk][Id ,, M1]}}}];
        mauto 4.
      eapply exp_eq_sub_cong_typ2'; mauto 4.
      eapply wf_sub_eq_p_extend; mauto 4.
    }

    econstructor; mauto 3.
    + econstructor; mauto 4.
    + eapply wf_conv; mauto 2.
      * eapply exp_sub_typ; mauto 3.
        econstructor; mauto 4.
      * symmetry.
        etransitivity.
        -- eapply wf_exp_eq_eq_sub; mauto.
        -- econstructor; mauto 3.
           ++
             eapply wf_exp_eq_conv;
             [eapply id_sub_lookup_var1 with (B:=B) | |];
               mauto 4.
           ++ eapply wf_exp_eq_conv;
             [eapply id_sub_lookup_var0 with (B:=B) | |];
               mauto 4.

  (** presup_exp_eq cases *)
  - assert {{ Γ ⊢s Id ,, N ≈ Id ,, N' : Γ, ℕ }} by mauto 4.
    assert {{ Γ ⊢ B[Id ,, N] ≈ B[Id ,, N'] : Type@i }} by mauto.
    assert {{ Γ ⊢ B[Id ,, N] ≈ B'[Id ,, N'] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Id ,, zero] ≈ B'[Id ,, zero] : Type@i }} by mauto.
    assert {{ Γ ⊢ NZ' : B'[Id ,, zero] }} by mauto.
    assert {{ Γ, ℕ, B ⊢ NS' : B'[WkWksucc] }} by (eapply wf_conv; mauto 4).
    assert {{ Γ, ℕ, B' ⊢ NS' : B'[WkWksucc] }} by mauto 4.
    assert {{ Γ ⊢ rec N' return B' | zero -> NZ' | succ -> NS' end : B'[Id ,, N'] }} by mauto 4.
    eapply wf_conv...

  - assert {{ Γ ⊢ B[(Id,,N)][σ] ≈ B[(Id,,N)∘σ] : Type@i }} by mauto 4.
    assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, ℕ }} by mauto.
    assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[(Id,,N)][σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 4.
    eapply wf_conv...

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
    assert {{ Γ' ⊢ B[WkWksucc][q (q σ)] ≈ B[q σ][WkWksucc] : Type@i }} by mauto.
    assert {{ Γ' ⊢ NS[q (q σ)] : B[q σ][WkWksucc] }} by mauto 4.
    eapply wf_conv...

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
    assert {{ Γ ⊢ λ B[σ] N[q σ] : Π B[σ] C[q σ] }} by mauto 4.
    eapply wf_conv...

  - assert {{ Δ ⊢ B : Type@(max i i0) }} by mauto using lift_exp_max_left.
    assert {{ Δ, B ⊢ C : Type@(max i i0) }} by mauto using lift_exp_max_right.
    enough {{ Δ ⊢ Π B C : Type@(max i i0) }}...

  - assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto.
    assert {{ Γ ⊢ B ≈ B[Id] : Type@i }} by mauto.
    assert {{ Γ ⊢ L ≈ L' : B[Id] }} by mauto 4.
    assert {{ Γ ⊢s Id ,, L ≈ Id ,, L' : Γ, B }} by mauto.
    assert {{ Γ ⊢ C[Id ,, L] ≈ C[Id ,, L'] : Type@i }} by mauto 4.
    eapply wf_conv...

  - assert {{ Γ ⊢ N[σ] : Π B[σ] C[q σ] }} by (eapply wf_conv; mauto).
    assert {{ Δ ⊢ L : B[Id] }} by mauto 4.
    assert {{ Γ ⊢s (Id ,, L)∘σ ≈ Id∘σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Γ ⊢s (Id ,, L)∘σ ≈ σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Δ ⊢s Id ,, L : Δ, B }} by mauto.
    assert {{ Γ ⊢s (Id ,, L)∘σ : Δ, B }} by mauto.
    assert {{ Γ ⊢ C[(Id ,, L)∘σ] ≈ C[σ ,, L[σ]] : Type@i }} by mauto.
    assert {{ Γ ⊢ C[Id ,, L][σ] ≈ C[σ ,, L[σ]] : Type@i }} by mauto 4.
    eapply wf_conv...

  - assert {{ Γ ⊢ B[σ] : Type@i }} by mauto.
    assert {{ Γ, B[σ] ⊢ C[q σ] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ N[σ] : Π B[σ] C[q σ] }} by (eapply wf_conv; mauto 4).
    assert {{ Γ ⊢ L[σ] : B[σ] }} by mauto.
    assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, L[σ]) ≈ σ ,, L[σ] : Δ, B }} by mauto.
    assert {{ Γ ⊢s Id ,, L[σ] : Γ, B[σ] }} by mauto.
    assert {{ Γ ⊢s q σ∘(Id ,, L[σ]) : Δ, B }} by mauto.
    assert {{ Γ ⊢ C[q σ∘(Id ,, L[σ])] ≈ C[σ ,, L[σ]] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ C[q σ][(Id ,, L[σ])] ≈ C[σ ,, L[σ]] : Type@i }} by mauto 4.
    eapply wf_conv...

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
    assert {{ Γ, B ⊢ M[Wk] #0 : C[q Wk ∘ Id0] }} by (eapply wf_conv; mauto 4).
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
    assert {{ Γ, B, B[Wk] ⊢ #0 : B[Wk∘Wk] }} by (eapply wf_conv; mauto 3).
    assert {{ Γ, B ⊢s q Wk ∘ Id0 ≈ (Wk∘Wk)∘Id0 ,, #0[Id0] : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ≈ Wk∘(Wk∘Id0) : Γ }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ≈ Wk∘Id : Γ }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0 : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0 ≈ #0[Id] : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[Wk][Id] }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[Wk∘Id] }} by (eapply wf_exp_eq_conv; mauto 4).
    assert {{ Γ, B ⊢ B[Wk∘Id] ≈ B[(Wk∘Wk)∘Id0] : Type@i }} by mauto.
    assert {{ Γ, B ⊢ #0[Id0] ≈ #0[Id] : B[(Wk∘Wk)∘Id0] }} by mauto.
    assert {{ Γ, B ⊢s (Wk∘Wk)∘Id0 ,, #0[Id0] ≈ Wk∘Id ,, #0[Id] : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s Wk∘Id ,, #0[Id] ≈ Id : Γ, B }} by mauto.
    assert {{ Γ, B ⊢s q Wk ∘ Id0 ≈ Id : Γ, B }} by mauto.
    assert {{ Γ, B ⊢ C[q Wk ∘ Id0] ≈ C[Id] : Type@i }} by mauto 4.
    enough {{ Γ, B ⊢ M[Wk] #0 : C }}...

  - econstructor...
  - eapply wf_conv...
  - assert {{ Γ ⊢s σ ,, M1[σ] : Δ, B}} by mauto.
    assert {{ Δ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Δ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] : Type@i}} by mauto.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk ∘ (σ,,M1[σ])]}}};
        [mauto | eapply exp_eq_sub_cong_typ2'; mauto].
    }
    assert {{ Γ ⊢ M2[σ] : B[Wk][σ ,, M1[σ]]}}.
    {
      eapply wf_conv with (A:={{{B[σ]}}});
        mauto 2.
    }
    assert {{ Γ ⊢s σ ,, M1[σ] ,, M2[σ] : Δ, B, B[Wk]}} by mauto 4.
    assert {{ Δ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).

    assert {{Γ ⊢ B[Wk][Wk][σ,,M1[σ],,M2[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk][Wk ∘ (σ,,M1[σ],,M2[σ])]}}};
        [mauto 4 | transitivity {{{B[Wk][σ,,M1[σ]]}}}];
        [| transitivity {{{B[Wk ∘ (σ,,M1[σ])]}}};
           [mauto 4 | ]];
        eapply exp_eq_sub_cong_typ2';
        mauto 4.
    }

    eapply wf_conv;
      [econstructor | |]; mauto 3.
    + eapply exp_sub_typ; try eassumption.
      econstructor; mauto 2.
      eapply wf_conv; mauto 2.
      transitivity {{{Eq (B[σ]) (M1[σ]) (M2[σ])}}};
        [mauto 4 | symmetry].
      etransitivity;
        [econstructor; mauto |].

      econstructor; eauto.
      * eapply wf_exp_eq_conv; mauto 4 using sub_lookup_var1.
      * eapply wf_exp_eq_conv;
          [eapply sub_lookup_var0 with (B:=B)| |];
          mauto 4.

    + assert {{ Δ ⊢s Id ,, M1 : Δ, B}} by mauto 4.
      assert {{ Δ , B ⊢ B[Wk] : Type@i }} by mauto 4.
      assert {{ Δ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
      assert {{ Δ ⊢ B[Wk][Id,,M1] ≈ B : Type@i }}.
      {
        transitivity {{{B[Wk ∘ (Id,,M1)]}}};
          [| transitivity {{{B[Id]}}}];
          mauto 3.
        eapply exp_eq_sub_cong_typ2'; mauto 3.
      }
      assert {{ Δ ⊢s Id ,, M1 ,, M2 : Δ, B , B[Wk]}}.
      {
        econstructor; mauto 3.
        eapply wf_conv; mauto 2.
      }
      assert {{ Δ ⊢ B[Wk][Wk][Id ,, M1 ,, M2] ≈ B : Type@i }}.
      {
        transitivity {{{B[Wk][Wk ∘ (Id ,, M1 ,, M2)]}}};
          [| transitivity {{{B[Wk][Id ,, M1]}}}];
          mauto 4.
        eapply exp_eq_sub_cong_typ2'; mauto 4.
        eapply wf_sub_eq_p_extend; mauto 4.
      }
      assert {{ Δ ⊢L : (Eq (B[Wk][Wk]) #1 #0) [ Id ,, M1 ,, M2]}}.
      {
        eapply wf_conv; mauto 2.
        symmetry.
        etransitivity.
        - eapply wf_exp_eq_eq_sub; mauto.
        - econstructor; mauto 3.
          + eapply wf_exp_eq_conv;
              [eapply id_sub_lookup_var1 with (B:=B) | |];
              mauto 4.
          + eapply wf_exp_eq_conv;
              [eapply id_sub_lookup_var0 with (B:=B) | |];
              mauto 4.
      }
      assert {{ Δ ⊢s Id ,, M1 ,, M2 ,, L : Δ, B , B[Wk], Eq (B[Wk][Wk]) #1 #0}} by mauto 4.

      transitivity {{{ C[(Id,,M1,,M2,,L) ∘ σ ] }}};
        [eapply exp_eq_sub_compose_typ | eapply exp_eq_sub_cong_typ2'];
        mauto 3.

      transitivity {{{(Id,,M1,,M2) ∘ σ ,, L[σ]}}};
        [econstructor; mauto 3 |].
      econstructor; mauto 3.
      * transitivity {{{(Id,,M1) ∘ σ ,, M2[σ]}}}.
        econstructor; mauto 4.
        econstructor; mauto 3.
        eapply exp_eq_refl.
        eapply wf_conv; mauto 3.
        eapply exp_eq_sub_cong_typ2'; mauto 3.
      * eapply exp_eq_refl.
        eapply wf_conv; mauto 3.

  - assert {{ Δ ⊢s Id ,, M1 : Δ, B}} by mauto 4.
    assert {{ Δ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Δ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] : Type@i}} by mauto.
    assert {{ Γ ⊢ B[σ] : Type @ i }} by mauto 3.
    assert {{ Γ ⊢ M1[σ] : B[σ] }} by mauto 3.
    assert {{ Γ ⊢ M2[σ] : B[σ] }} by mauto 3.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk ∘ (σ,,M1[σ])]}}};
        [| eapply exp_eq_sub_cong_typ2']; mauto 4.
    }
    assert {{ Γ ⊢ M2[σ] : B[Wk][σ ,, M1[σ]]}} by mauto 3.
    assert {{ Γ ⊢s σ,, M1[σ] : Δ,B}} by mauto 3.
    assert {{ Γ ⊢s σ ,, M1[σ] ,, M2[σ] : Δ, B, B[Wk]}} by mauto 3.
    assert {{ Δ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).

    assert {{Γ ⊢ B[Wk][Wk][σ,,M1[σ],,M2[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk][Wk ∘ (σ,,M1[σ],,M2[σ])]}}};
        [mauto 4 | transitivity {{{B[Wk][σ,,M1[σ]]}}}];
        mauto 2.
      eapply exp_eq_sub_cong_typ2';
        mauto 4.
    }
    assert {{ Γ ⊢ L[σ] : (Eq B M1 M2)[σ] }} by mauto 3.
    assert {{ Γ ⊢ L[σ] : Eq (B[σ]) (M1[σ]) (M2[σ]) }} by (eapply wf_conv; mauto 3).
    assert {{ Γ ⊢ #1[σ,,M1[σ],,M2[σ]] ≈ M1[σ] : B[Wk][Wk][σ,,M1[σ],,M2[σ]] }}.
    {
      eapply wf_exp_eq_conv;
        [eapply sub_lookup_var1 with (B:=B) | |];
        mauto 4.
    }
    assert {{ Γ ⊢ #0[σ,,M1[σ],,M2[σ]] ≈ M2[σ] : B[Wk][Wk][σ,,M1[σ],,M2[σ]] }}.
    {
      eapply wf_exp_eq_conv;
        [eapply sub_lookup_var0 with (B:=B) | |];
        mauto 4.
    }
    assert {{ Γ ⊢ L[σ] : (Eq (B[Wk][Wk]) #1 #0)[σ,,M1[σ],,M2[σ]] }}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
    }
    assert {{ Γ ⊢s σ,,M1[σ],,M2[σ],,L[σ] : Δ,B,B[Wk],Eq (B[Wk][Wk]) #1 #0}} by mauto 3.
    assert {{Γ, B[σ] ⊢s q σ : Δ, B}} by mauto 4.
    assert {{Γ, B[σ] ⊢ B[σ][Wk] : Type@i}} by mauto 4.
    assert {{Γ, B[σ], B[σ][Wk] ⊢ B[σ][Wk][Wk] : Type@i}} by mauto.
    assert {{Γ, B[σ], B[σ][Wk] ⊢ Eq (B[σ][Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 3; mauto).
    assert {{Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] : Type@i}}.
    {
      transitivity {{{B[Wk ∘ q σ]}}};
        [mauto 3 | transitivity {{{B[σ ∘ Wk]}}}];
        [eapply exp_eq_sub_cong_typ2'; mauto 3 | mauto].
    }
    assert {{⊢ Γ, B[σ], B[Wk][q σ] ≈ Γ, B[σ], B[σ][Wk]}} by (econstructor; mauto 3).
    assert {{Γ, B[σ], B[σ][Wk] ⊢s q (q σ) : Δ, B, B[Wk]}}.
    {
      eapply ctxeq_sub; [| eapply sub_q]; mauto 2.
    }
    assert {{Γ, B[σ],B[σ][Wk] ⊢ B[Wk][q σ ∘ Wk] : Type@i}} by mauto.
    assert {{Γ, B[σ],B[σ][Wk] ⊢ B[Wk][q σ ∘ Wk] ≈ B[σ][Wk][Wk] : Type@i}}.
    {
      transitivity {{{B[Wk][q σ][Wk]}}};
        [mauto |].
      eapply exp_eq_sub_cong_typ1; mauto 3.
    }
    assert {{Γ, B[σ],B[σ][Wk] ⊢ B[Wk][Wk][q (q σ)] ≈ B[σ][Wk][Wk] : Type@i}}.
    {
      transitivity {{{B[Wk][Wk ∘ q (q σ)]}}};
        [mauto 4| transitivity {{{B[Wk][q σ ∘ Wk]}}}];
        [eapply exp_eq_sub_cong_typ2'; mauto 4 | trivial].
    }
    assert {{Γ, B[σ], B[σ][Wk] ⊢ #1 : B[σ][Wk][Wk]}} by mauto.
    assert {{Γ, B[σ], B[σ][Wk] ⊢ Eq (B[σ][Wk][Wk]) #0 #0 : Type@i}} by (econstructor; mauto 3).
    assert {{Γ, B[σ], B[σ][Wk] ⊢ (Eq (B[Wk][Wk]) #1 #0)[q (q σ)] ≈ Eq (B[σ][Wk][Wk]) #1 #0 : Type@i}}.
    {
      transitivity {{{Eq (B[Wk][Wk][q (q σ)]) (#1[q (q σ)]) (#0[q (q σ)])}}};
        [econstructor; mauto 4 |].
      econstructor; mauto 2.
      - eapply wf_exp_eq_conv;
          [eapply ctxeq_exp_eq;[eassumption | eapply exp_eq_var_1_sub_q_sigma] | |];
          mauto 2.
      - eapply wf_exp_eq_conv.
        econstructor; [mauto 4 | eauto | eapply wf_conv; mauto].
        + mauto 2.
        + mauto 4.
    }
    assert {{Γ, B[σ], B[σ][Wk], Eq (B[σ][Wk][Wk]) #1 #0 ⊢s q (q (q σ)) : Δ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0}}.
    {
      eapply ctxeq_sub; [| eapply sub_q]; mauto 2.
      econstructor; mauto 3.
    }
    assert {{Γ, B[σ] ⊢s Id,,#0 : Γ, B[σ], B[σ][Wk]}} by mauto 4.
    assert {{Γ, B[σ] ⊢ B[σ][Wk][Wk][Id,,#0] ≈ B[σ][Wk] : Type@i}}.
    {
      transitivity {{{B[σ][Wk][Wk ∘ (Id,,#0)]}}};
        [mauto 4 |].
      transitivity {{{B[σ][Wk][Id]}}};
        [| mauto 3].
      eapply exp_eq_sub_cong_typ2'; mauto 4.
    }

    assert {{Γ, B[σ] ⊢s Id,,#0,,refl (B[σ][Wk]) #0 : Γ, B[σ], B[σ][Wk], Eq (B[σ][Wk][Wk]) #1 #0}}.
    {
      econstructor; mauto 3.
      eapply wf_conv;
        [econstructor | |];
        mauto 2.
      - mauto 3.
      - symmetry.
        etransitivity; [econstructor; mauto 3 |].
        econstructor; eauto.
        + eapply wf_exp_eq_conv; mauto 2.
          transitivity {{{#0[Id]}}}.
          * eapply wf_exp_eq_conv; [econstructor | |];
              mauto 3.
            mauto 4.
          * eapply wf_exp_eq_conv; mauto 4.
        + eapply wf_exp_eq_conv;
            [econstructor | |].
          * mauto 3.
          * mauto 2.
          * mauto 4.
          * mauto 2.
          * etransitivity; mauto 2.
    }
    assert {{Γ, B[σ] ⊢s q (q σ) ∘ (Id,,#0) ≈ q σ,,#0 : Δ, B, B[Wk]}}.
    {
      eapply sub_eq_q_sigma_id_extend;
        mauto 2.
      eapply wf_conv; mauto 3.
    }
    assert {{Γ, B[σ] ⊢ #0 : B[σ][Wk][Wk][Id,,#0]}} by (eapply wf_conv; mauto 3).
    assert {{Γ, B[σ] ⊢ #0[Id,,#0] ≈ #0 : B[σ][Wk][Id]}} by (econstructor; mauto 3).
    assert {{Γ, B[σ] ⊢ #0[Id,,#0] ≈ #0 : B[σ][Wk]}} by mauto 3.
    assert {{Γ, B[σ] ⊢ #0[Id,,#0] ≈ #0 : B[σ][Wk][Wk][Id,,#0]}} by mauto 4.
    assert {{Γ, B[σ] ⊢ (Eq (B[σ][Wk][Wk]) #0 #0)[Id,,#0] ≈ Eq (B[σ][Wk]) #0 #0 : Type@i}}.
    {
      etransitivity; econstructor; mauto 3.
    }
    assert {{Γ, B[σ] ⊢s (q (q σ) ∘ Wk) ∘ (Id,,#0,,refl (B[σ][Wk]) #0) : Δ, B, B[Wk]}}.
    {
      econstructor; mauto 3.
      econstructor; mauto 3.
    }
    assert {{Γ, B[σ] ⊢s (q (q σ) ∘ Wk) ∘ (Id,,#0,,refl (B[σ][Wk]) #0)
                  ≈ q (q σ) ∘ (Id,,#0) : Δ, B, B[Wk]}}.
    {
      transitivity {{{q (q σ) ∘ (Wk ∘ (Id,,#0,,refl (B[σ][Wk]) #0))}}};
        [mauto 4 |].
      econstructor; mauto 3.
      eapply wf_sub_eq_p_extend with (A:={{{Eq (B[σ][Wk][Wk]) #0 #0}}}); mauto 2.

      eapply wf_conv;
        [econstructor; mauto 3 | eapply exp_sub_typ; mauto 3 |].

      symmetry.
      etransitivity;
        [econstructor; mauto 3 |].
      econstructor; mauto 3.
    }
    assert {{Γ, B[σ] ⊢s (q (q σ) ∘ Wk) ∘ (Id,,#0,,refl (B[σ][Wk]) #0)
                  ≈ q σ,,#0 : Δ, B, B[Wk]}} by mauto 4.
    assert {{Γ, B[σ] ⊢ B[σ][Wk][Wk][Id,,#0] ≈ B[Wk][q σ] : Type@i}} by mauto 3.
    assert {{Γ, B[σ] ⊢ B[Wk][Wk][q σ,,#0] ≈ B[Wk][q σ] : Type@i}}.
    {
      transitivity {{{B[Wk][Wk ∘ (q σ,,#0)]}}};
        [eapply exp_eq_sub_compose_typ; mauto 4 |].
      symmetry.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
      symmetry.
      mauto 4.
    }
    assert {{Γ, B[σ] ⊢s q σ,,#0 : Δ, B, B[Wk] }} by (econstructor; mauto 3).
    assert {{Γ, B[σ] ⊢ B[Wk][Wk][q σ,,#0] : Type@i}} by mauto 3.
    assert {{Γ, B[σ] ⊢ B[Wk][Wk][q σ,,#0] ≈ B[σ][Wk] : Type@i}} by mauto 4.
    assert {{ Γ, B[σ] ⊢ #0[q σ,,#0] ≈ # 0 : B[σ][Wk] }}.
    {
      eapply wf_exp_eq_conv;
        [econstructor | |];
        mauto 2.
      mauto 3.
    }
    assert {{ Γ, B[σ] ⊢ #0[q σ,,#0] ≈ # 0 : B[Wk][Wk][q σ,,#0] }} by mauto 3.

    assert {{ Γ, B[σ] ⊢s σ ∘ Wk : Δ }} by mauto 4.
    assert {{ Γ, B[σ] ⊢ # 0 : B[σ][Wk] }} by mauto 2.
    assert {{ Γ, B[σ] ⊢ B[σ][Wk] ≈ B[σ ∘ Wk] : Type@i }} by mauto 4.
    assert {{ Γ, B[σ] ⊢ # 0 : B[σ ∘ Wk] }} by mauto 3.

    assert {{ Γ, B[σ] ⊢ #1[q σ,,#0] ≈ # 0 : B[σ][Wk] }}.
    {
      eapply wf_exp_eq_conv with (A:={{{B[σ ∘ Wk]}}});
        [eapply sub_lookup_var1; eauto | |];
        mauto 2.
    }
    assert {{ Γ, B[σ] ⊢ #1[q σ,,#0] ≈ # 0 : B[Wk][Wk][q σ,,#0] }} by mauto 3.

    assert {{Γ, B[σ] ⊢s q (q (q σ)) ∘ (Id,,#0,,refl (B[σ][Wk]) #0)
                  ≈ (q (q σ) ∘ (Id,,#0)),,refl (B[σ][Wk]) #0
          : Δ, B, B[Wk], Eq (B[Wk][Wk]) # 1 # 0}}.
    {
      etransitivity;
        [eapply wf_sub_eq_extend_compose; mauto 2; mauto 4 |].

      - eapply wf_conv; mauto 3.
        + mauto.
        + symmetry.
          transitivity {{{(Eq (B[Wk][Wk]) #1 #0)[q (q σ)][Wk]}}};
            [mauto |].
          eapply exp_eq_sub_cong_typ1; mauto 4.
      - econstructor; mauto 3.

        eapply wf_exp_eq_conv.
        econstructor; mauto 3.
        + eapply wf_conv; [econstructor | |]; mauto 3.
        + eapply exp_sub_typ; mauto 3.
        + etransitivity; eauto.
          symmetry.
          etransitivity; [| etransitivity].
          * eapply exp_eq_sub_cong_typ2'; mauto 3.
          * econstructor; mauto 4.
          * econstructor; mauto 2.
    }

    assert {{⊢ Δ, B, B[Wk]}} by mauto 3.
    assert {{Δ, B, B[Wk] ⊢ #0 : B[Wk][Wk]}} by mauto 4.
    assert {{Δ, B, B[Wk] ⊢ #1 : B[Wk][Wk]}} by mauto 4.
    assert {{Γ, B[σ] ⊢ B[Wk][Wk][q (q σ) ∘ (Id,,#0)] ≈ B[Wk][q σ] : Type@i}} by mauto 4.
    assert {{Γ, B[σ] ⊢ B[Wk][Wk][q (q σ) ∘ (Id,,#0)] ≈ B[σ][Wk] : Type@i}} by mauto 4.

    assert {{ Γ, B[σ] ⊢ #0[q (q σ) ∘ (Id,,#0)] ≈ # 0 : B[σ][Wk] }}.
    {
      transitivity {{{#0[q σ,,#0]}}}.
      - symmetry.
        eapply wf_exp_eq_conv;
          [econstructor | |]; mauto 2.
      - eauto.
    }
    assert {{ Γ, B[σ] ⊢ #0[q (q σ) ∘ (Id,,#0)] ≈ # 0 : B[Wk][Wk][q (q σ) ∘ (Id,,#0)] }} by
      (eapply wf_exp_eq_conv; mauto 3).

    assert {{ Γ, B[σ] ⊢ #1[q (q σ) ∘ (Id,,#0)] ≈ # 0 : B[σ][Wk] }}.
    {
      transitivity {{{#1[q σ,,#0]}}}.
      - symmetry.
        eapply wf_exp_eq_conv;
          [econstructor | |]; mauto 2.
      - eauto.
    }
    assert {{ Γ, B[σ] ⊢ #1[q (q σ) ∘ (Id,,#0)] ≈ # 0 : B[Wk][Wk][q (q σ) ∘ (Id,,#0)] }} by
      (eapply wf_exp_eq_conv; mauto 3).

    assert {{Γ, B[σ] ⊢s q (q (q σ)) ∘ (Id,,#0,,refl (B[σ][Wk]) #0)
                  ≈ q σ,,#0,,refl (B[σ][Wk]) #0 : Δ, B, B[Wk], Eq (B[Wk][Wk]) # 1 # 0}}.
    {
      etransitivity; eauto.
      econstructor; mauto 3.
      eapply exp_eq_refl.
      eapply wf_conv; mauto 3.
      symmetry.
      etransitivity.
      - econstructor; mauto 2.
      - econstructor; mauto 2.
    }

    assert {{Γ, B[σ] ⊢s Id ∘ q σ : Δ, B}} by mauto 3.
    assert {{Γ, B[σ] ⊢s Id ∘ q σ ≈ q σ : Δ, B}} by mauto 3.
    assert {{Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ ∘ Wk]}} by mauto 3.
    assert {{Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ][Wk]}} by mauto 3.
    assert {{Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[Wk][q σ]}} by mauto 4.
    assert {{Γ, B[σ] ⊢s (Id,,#0) ∘ q σ : Δ, B, B[Wk]}} by (econstructor; mauto 3).
    assert {{Γ, B[σ] ⊢s (Id,,#0) ∘ q σ ≈ q σ,,#0 : Δ, B, B[Wk]}}.
    {
      etransitivity.
      - eapply wf_sub_eq_extend_compose; mauto 3.
      - econstructor; mauto 3.
        eapply wf_exp_eq_conv; mauto 2.
        eapply exp_eq_sub_cong_typ2'; mauto 3.
    }

    assert {{Δ, B ⊢ B[Wk][Wk][Id,,#0] ≈ B[Wk] : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id,,#0)]}}}; [ |transitivity{{{B[Wk][Id]}}}].
      - eapply exp_eq_sub_compose_typ; mauto 3.
      - eapply exp_eq_sub_cong_typ2'; mauto 3.
        econstructor; mauto 3.
      - mauto 3.
    }
    assert {{Δ, B ⊢ #0[Id ,, #0] ≈ #0 : B[Wk]}}.
    {
      eapply wf_exp_eq_conv;
      [econstructor | |]; mauto 3.
    }
    assert {{Δ, B ⊢ B[Wk][Wk][Id,,#0] : Type@i }} by (eapply exp_sub_typ; mauto 3).
    assert {{Δ, B ⊢ #0[Id ,, #0] ≈ #0 : B[Wk][Wk][Id,,#0]}} by (eapply wf_exp_eq_conv; mauto 2).
    assert {{Δ, B ⊢ #1[Id ,, #0] ≈ #0 : B[Wk]}}.
    {
      transitivity {{{#0[Id]}}}; mauto 3.
      eapply wf_exp_eq_conv;
        [econstructor | |]; mauto 3.
      eapply wf_conv; mauto 3.
      symmetry.
      mauto 3.
    }
    assert {{Δ, B ⊢ #1[Id ,, #0] ≈ #0 : B[Wk][Wk][Id,,#0]}} by (eapply wf_exp_eq_conv; mauto 2).

    assert {{Δ, B ⊢ refl (B[Wk]) #0 : (Eq (B[Wk][Wk]) #1 #0)[Id ,, #0]}}.
    {
      eapply wf_conv; mauto 3.
      - mauto 4.
      - symmetry.
        etransitivity.
        + econstructor; mauto 3.
        + econstructor; mauto 3.
    }

    assert {{ Γ, B[σ] ⊢ (Eq B[Wk] #0 #0)[q σ] ≈ Eq B[σ][Wk] #0 #0 : Type@i }}.
    {
      etransitivity;
        [econstructor; mauto 2 |];
        mauto 3.
    }

    assert {{ Γ, B[σ] ⊢ B[Wk][Wk][(Id,,#0)∘q σ] ≈ B[σ][Wk] : Type@i }} by mauto 3.

    assert {{ Γ, B[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : B[σ][Wk] }}.
    {
      transitivity {{{#1[q σ,,#0]}}};
        [eapply wf_exp_eq_conv |];
        mauto 3.
    }
    assert {{ Γ, B[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : B[Wk][Wk][(Id,,#0)∘q σ] }} by mauto 4.

    assert {{ Γ, B[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : B[σ][Wk] }}.
    {
      transitivity {{{#0[q σ,,#0]}}};
        [eapply wf_exp_eq_conv |];
        mauto 3.
    }
    assert {{ Γ, B[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : B[Wk][Wk][(Id,,#0)∘q σ] }} by mauto 4.

    assert {{ Γ, B[σ] ⊢ (Eq B[Wk][Wk] #1 #0)[(Id,,#0)∘q σ] ≈ Eq B[σ][Wk] #0 #0 : Type@i }}.
    {
      etransitivity; econstructor; mauto 2.
    }

    assert {{Γ, B[σ] ⊢s (Id,,#0,,refl (B[Wk]) #0) ∘ q σ
                  ≈ q σ,,#0,,refl (B[σ][Wk]) #0 : Δ, B, B[Wk], Eq (B[Wk][Wk]) # 1 # 0}}.
    {
      etransitivity.
      - eapply wf_sub_eq_extend_compose; mauto 3.
      - econstructor; mauto 2.
        etransitivity.
        + eapply wf_exp_eq_conv;
            [eapply wf_exp_eq_refl_sub; mauto 3 |
             eapply exp_sub_typ; mauto 3 |].
          mauto 3.
        + eapply wf_exp_eq_conv;
            [econstructor | |];
            mauto 2.
          etransitivity; mauto 2.
    }

    assert {{ Δ, B ⊢s Id,,#0,,refl B[Wk] #0 : ((Δ, B), B[Wk]), Eq B[Wk][Wk] #1 #0 }} by mauto 4.

    assert {{ Γ ⊢s Id,,M1[σ] : Γ,B[σ]}} by mauto 2.
    assert {{ Γ ⊢ B[σ][Wk][Id ,, M1[σ]] ≈ B[σ] : Type@i}}.
    {
      etransitivity;
        [eapply exp_eq_sub_compose_typ; mauto 3 |];
        transitivity {{{B[σ][Id]}}}; mauto 2.
      symmetry.
      eapply exp_eq_sub_cong_typ2';
        mauto 3.
    }
    assert {{ Γ ⊢ M2[σ] : B[σ][Wk][Id ,, M1[σ]]}} by mauto 4.
    assert {{ Γ ⊢s Id ,, M1[σ] ,, M2[σ] : Γ, B[σ], B[σ][Wk]}} by mauto 3.

    assert {{ Γ ⊢ B[σ][Wk][Wk][Id,,M1[σ],,M2[σ]] ≈ B[σ] : Type@i }}.
    {
      etransitivity;
        [eapply exp_eq_sub_compose_typ; mauto 3 |];
        transitivity {{{B[σ][Wk][Id,,M1[σ]]}}}; mauto 3.
      symmetry.
      eapply exp_eq_sub_cong_typ2';
        mauto 3.
    }

    assert {{ Γ ⊢ #1[Id,,M1[σ],,M2[σ]] ≈ M1[σ] : B[σ] }}.
    {
      transitivity {{{#0[Id,,M1[σ]]}}};
        [eapply wf_exp_eq_conv | eapply wf_exp_eq_conv; econstructor];
        mauto 3.
    }
    assert {{ Γ ⊢ #1[Id,,M1[σ],,M2[σ]] ≈ M1[σ] : B[σ][Wk][Wk][Id,,M1[σ],,M2[σ]] }} by mauto 4.

    assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : B[σ] }}
      by (eapply wf_exp_eq_conv; mauto 3).
    assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : B[σ][Wk][Wk][Id,,M1[σ],,M2[σ]] }} by mauto 4.

    assert {{ Γ ⊢ (Eq B[σ][Wk][Wk] #1 #0)[Id ,, M1[σ] ,, M2[σ]] ≈ Eq B[σ] M1[σ] M2[σ] : Type@i }}
      by (etransitivity; econstructor; mauto 3).
    assert {{ Γ ⊢ L[σ] : (Eq B[σ][Wk][Wk] #1 #0)[Id ,, M1[σ] ,, M2[σ]] }} by mauto 4.

    assert {{ Γ ⊢s Id ,, M1[σ] ,, M2[σ] ,, L[σ] : Γ, B[σ], B[σ][Wk], Eq B[σ][Wk][Wk] #1 #0}} by mauto 3.

    assert {{ (Γ, B[σ]), B[σ][Wk] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] : Type@i }}.
    {
      transitivity {{{B[Wk][q σ][Wk]}}};
        [symmetry;
         eapply exp_eq_sub_compose_typ; mauto 3 |].
      eapply exp_eq_sub_cong_typ1; mauto 3.
    }

    assert {{ (Γ, B[σ]), B[σ][Wk] ⊢ #0 : B[Wk][q σ∘Wk] }}
      by (eapply wf_conv; mauto 3).

    assert {{ ((Γ, B[σ]), B[σ][Wk]), Eq B[σ][Wk][Wk] #1 #0 ⊢s q (q σ)∘Wk : Δ,B,B[Wk] }} by mauto 4.
    assert {{ ((Γ, B[σ]), B[σ][Wk]), Eq B[σ][Wk][Wk] #1 #0 ⊢ (Eq B[Wk][Wk] #1 #0)[q (q σ)∘Wk] ≈ (Eq B[σ][Wk][Wk] #1 #0)[Wk] : Type@i }}.
    {
      transitivity {{{(Eq B[Wk][Wk] #1 #0)[q (q σ)][Wk]}}};
        [symmetry;
         eapply exp_eq_sub_compose_typ; mauto 3 |].
      eapply exp_eq_sub_cong_typ1; mauto 3.
    }


    assert {{ Δ,B,B[Wk] ⊢ Eq B[Wk][Wk] #1 #0 : Type@i }} by mauto 3.
    assert {{ ((Γ, B[σ]), B[σ][Wk]), Eq B[σ][Wk][Wk] #1 #0 ⊢ #0 : (Eq B[Wk][Wk] #1 #0)[q (q σ)∘Wk] }}.
    {
      eapply wf_conv; mauto 3.
    }

    assert {{ Γ ⊢s (q σ ∘ Wk) ∘ (Id,,M1[σ],,M2[σ]) : Δ, B }}
             by (econstructor; mauto 4).
    assert {{ Γ ⊢s (q σ ∘ Wk) ∘ (Id,,M1[σ],,M2[σ]) ≈ σ,,M1[σ] : Δ, B }}.
    {
      etransitivity;
        [eapply wf_sub_eq_compose_assoc; mauto 3 |].
      etransitivity;
        [eapply wf_sub_eq_compose_cong;
         [eapply wf_sub_eq_p_extend with (A:={{{B[σ][Wk]}}}) | eapply sub_eq_refl]  |];
        mauto 3.
    }

    assert {{ Γ ⊢ B[Wk][(q σ∘Wk)∘(Id,,M1[σ],,M2[σ])] ≈ B[σ] : Type@i }}.
    {
      transitivity {{{B[Wk][σ,,M1[σ]]}}};
        [eapply exp_eq_sub_cong_typ2' |]; mauto 3.
    }
    assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : B[Wk][(q σ∘Wk)∘(Id,,M1[σ],,M2[σ])] }} by mauto 4.
    assert {{ Γ ⊢s q (q σ) ∘ (Id,,M1[σ],,M2[σ]) ≈ σ,,M1[σ],,M2[σ] : Δ, B, B[Wk] }}.
    {
      etransitivity;
        [eapply wf_sub_eq_extend_compose; mauto 4 |].
      econstructor; mauto 2.
    }
    assert {{ Γ ⊢s (q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,L[σ]) : (Δ, B), B[Wk] }}
      by (econstructor; mauto 4).
    assert {{ Γ ⊢s (q (q σ) ∘ Wk) ∘ (Id,,M1[σ],,M2[σ],,L[σ]) ≈ σ,,M1[σ],,M2[σ] : Δ, B, B[Wk] }}.
    {
      etransitivity;
        [eapply wf_sub_eq_compose_assoc; mauto 3 |].
      etransitivity;
        [eapply wf_sub_eq_compose_cong;
         [eapply wf_sub_eq_p_extend with (A:={{{Eq B[σ][Wk][Wk] #1 #0}}}) | eapply sub_eq_refl]  |];
        mauto 3.
    }

    assert {{ Γ ⊢ (Eq B[Wk][Wk] #1 #0)[σ,,M1[σ],,M2[σ]] ≈ Eq B[σ] M1[σ] M2[σ] : Type@i }}.
    {
      etransitivity;
        econstructor; mauto 3.
    }
    assert {{ Γ ⊢ (Eq B[Wk][Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,L[σ])] ≈ Eq B[σ] M1[σ] M2[σ] : Type@i }}.
    {
      transitivity {{{(Eq B[Wk][Wk] #1 #0)[σ,,M1[σ],,M2[σ]]}}};
        [eapply exp_eq_sub_cong_typ2' |]; mauto 3.
    }
    assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ],,L[σ]] ≈ L[σ] : (Eq B[Wk][Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,L[σ])] }}.
    {
      eapply wf_exp_eq_conv with (A:={{{Eq B[σ] M1[σ] M2[σ]}}});
        econstructor; mauto 3.
    }
    assert {{ Γ ⊢s q (q (q σ)) ∘ (Id,,M1[σ],,M2[σ],,L[σ]) ≈ σ,,M1[σ],,M2[σ],,L[σ] : Δ, B, B[Wk], Eq B[Wk][Wk] #1 #0 }}.
    {
      etransitivity;
        [eapply wf_sub_eq_extend_compose; mauto 4 |].
      econstructor; mauto 2.
    }

    assert {{Γ, B[σ] ⊢s (Id,,#0,,refl (B[Wk]) #0) ∘ q σ
                  ≈ q (q (q σ)) ∘ (Id,,#0,,refl (B[σ][Wk]) #0)
          : Δ, B, B[Wk], Eq (B[Wk][Wk]) # 1 # 0}} by mauto 3.

    eapply wf_conv;
    [econstructor | |];
      mauto 2.
    + eapply wf_conv; mauto 3.
    + etransitivity;
        [eapply exp_eq_sub_compose_typ | eapply exp_eq_sub_cong_typ2'];
        mauto 3.

  - eexists.
    eapply exp_sub_typ; mauto 2.
    assert {{ Δ ⊢s Id ,, M1 : Δ, B}} by mauto 4.
    assert {{ Δ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Δ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] : Type@i}} by mauto.
    assert {{ Γ ⊢ B[σ] : Type @ i }} by mauto 3.
    assert {{ Γ ⊢ M1[σ] : B[σ] }} by mauto 3.
    assert {{ Γ ⊢ M2[σ] : B[σ] }} by mauto 3.
    assert {{ Γ ⊢ B[Wk][σ ,, M1[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk ∘ (σ,,M1[σ])]}}};
        [| eapply exp_eq_sub_cong_typ2']; mauto 4.
    }
    assert {{ Γ ⊢ M2[σ] : B[Wk][σ ,, M1[σ]]}} by mauto 3.
    assert {{ Γ ⊢s σ,, M1[σ] : Δ,B}} by mauto 3.
    assert {{ Γ ⊢s σ ,, M1[σ] ,, M2[σ] : Δ, B, B[Wk]}} by mauto 3.
    assert {{ Δ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).

    assert {{Γ ⊢ B[Wk][Wk][σ,,M1[σ],,M2[σ]] ≈ B[σ] : Type@i}}.
    {
      transitivity {{{B[Wk][Wk ∘ (σ,,M1[σ],,M2[σ])]}}};
        [mauto 4 | transitivity {{{B[Wk][σ,,M1[σ]]}}}];
        mauto 2.
      eapply exp_eq_sub_cong_typ2';
        mauto 4.
    }
    assert {{ Γ ⊢ L[σ] : (Eq B M1 M2)[σ] }} by mauto 3.
    assert {{ Γ ⊢ L[σ] : Eq (B[σ]) (M1[σ]) (M2[σ]) }} by (eapply wf_conv; mauto 3).
    assert {{ Γ ⊢ L[σ] : (Eq (B[Wk][Wk]) #1 #0)[σ,,M1[σ],,M2[σ]] }}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
        + eapply wf_exp_eq_conv;
            [eapply sub_lookup_var1 with (B:=B) | |];
            mauto 4.
        + eapply wf_exp_eq_conv;
            [eapply sub_lookup_var0 with (B:=B) | |];
            mauto 4.
    }
    mauto 3.

  - eapply wf_conv; [mauto 3 | mauto 2 |].
    symmetry. mauto 3.

  - assert {{ Γ ⊢s Id ,, M1 : Γ, B}} by mauto 4.
    assert {{ Γ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,M1] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,M1)]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, M1 ,, M2 : Γ, B , B[Wk]}}.
    {
      econstructor; mauto 3.
      eapply wf_conv; mauto 2.
    }
    assert {{ Γ ⊢ B[Wk][Wk][Id ,, M1 ,, M2] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id ,, M1 ,, M2)]}}};
        [| transitivity {{{B[Wk][Id ,, M1]}}}];
        mauto 4.
      eapply exp_eq_sub_cong_typ2'; mauto 4.
      eapply wf_sub_eq_p_extend; mauto 4.
    }
    assert {{ Γ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B[Wk][Wk][Id,,M1,,M2] }}.
    {
      eapply wf_exp_eq_conv;
        [eapply id_sub_lookup_var1 with (B:=B) | |];
        mauto 4.
    }
    assert {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B[Wk][Wk][Id,,M1,,M2] }}.
    {
      eapply wf_exp_eq_conv;
        [eapply id_sub_lookup_var0 with (B:=B) | |];
        mauto 4.
    }
    assert {{ Γ ⊢L : (Eq (B[Wk][Wk]) #1 #0) [ Id ,, M1 ,, M2]}}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, M1 ,, M2 ,, L : Γ, B , B[Wk], Eq (B[Wk][Wk]) #1 #0}} by mauto 4.
    assert {{ Γ ⊢ Eq B' M1' M2' : Type @ i }} by mauto 4.
    assert {{ Γ ⊢ Eq B' M1' M2' ≈ Eq B M1 M2 : Type @ i }} by (symmetry; mauto 3).

    assert {{ ⊢ Γ, B ≈ Γ, B' }} by mauto 3.
    assert {{ Γ , B ⊢ B'[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B' ⊢ B'[Wk] : Type@i }} by mauto 4.
    assert {{ Γ, B ⊢ B[Wk] ≈ B'[Wk] : Type@i }} by mauto 3.
    assert {{ Γ, B' ⊢ B[Wk] ≈ B'[Wk] : Type@i }} by mauto 3.
    assert {{ ⊢ Γ, B, B[Wk] ≈ Γ, B', B'[Wk] }} by mauto 4.

    assert {{ Γ, B', B'[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by mauto 3.
    assert {{ Γ, B', B'[Wk] ⊢ Eq (B'[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).
    assert {{ Γ, B, B[Wk] ⊢ Eq (B'[Wk][Wk]) # 1 # 0 : Type@i }} by mauto 3.
    assert {{ (Γ, B), B[Wk] ⊢ Eq B[Wk][Wk] #1 #0 ≈ Eq B'[Wk][Wk] #1 #0 : Type@i }} by (econstructor; mauto 4).

    assert {{ ⊢ Γ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0 ≈ Γ, B', B'[Wk], Eq (B'[Wk][Wk]) #1 #0 }} by mauto 3.

    assert {{ Γ, B ⊢ Eq B[Wk] #0 #0 : Type@i }} by (econstructor; mauto 2).
    assert {{ Γ, B ⊢ Eq B'[Wk] #0 #0 ≈ Eq B[Wk] #0 #0 : Type@i }} by (econstructor; mauto 3).

    assert {{ Γ, B ⊢ refl B'[Wk] #0 : Eq (B[Wk]) #0 #0 }}.
    {
      eapply wf_conv;
      [econstructor | |]; mauto 3.
    }
    assert {{ Γ, B ⊢ refl B[Wk] #0 : Eq (B[Wk]) #0 #0 }} by mauto 4.
    assert {{ Γ, B ⊢ refl B[Wk] #0 ≈ refl B'[Wk] #0 : Eq (B[Wk]) #0 #0 }} by mauto 3.
    assert {{ Γ, B ⊢s Id,,#0 : Γ, B, B[Wk] }} by mauto 3.
    assert {{ (Γ, B), B[Wk] ⊢ #1 : B[Wk][Wk] }} by mauto 4.
    assert {{ Γ, B ⊢s Wk∘(Id,,#0) : Γ, B }} by (econstructor; mauto 3).
    assert {{ Γ, B ⊢ B[Wk][Wk][Id,,#0] ≈ B[Wk] : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id,,#0)]}}};
        [eapply exp_eq_sub_compose_typ |
         transitivity {{{B[Wk][Id]}}} ];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ, B ⊢ #1[Id,,#0] ≈ #0 : B[Wk] }}.
    {
      transitivity {{{#0[Id]}}}.
      - eapply wf_exp_eq_conv;
          [eapply wf_exp_eq_var_S_sub with (A:={{{B[Wk]}}}) | |];
          mauto 3.
      - mauto 3.
    }
    assert {{ Γ, B ⊢ #1[Id,,#0] ≈ #0 : B[Wk][Wk][Id,,#0] }} by mauto 4.
    assert {{ Γ, B ⊢ #0[Id,,#0] ≈ #0 : B[Wk] }}.
    {
      eapply wf_exp_eq_conv;
        [eapply wf_exp_eq_var_0_sub with (A:={{{B[Wk]}}}) | |];
        mauto 3.
    }
    assert {{ Γ, B ⊢ #0[Id,,#0] ≈ #0 : B[Wk][Wk][Id,,#0] }} by mauto 4.
    assert {{ Γ, B ⊢ (Eq B[Wk][Wk] #1 #0)[Id,,#0] ≈ Eq (B[Wk]) #0 #0 : Type@i }}.
    {
      etransitivity; econstructor; mauto 3.
    }
    assert {{ Γ, B ⊢ refl B'[Wk] #0 : (Eq B[Wk][Wk] #1 #0)[Id,,#0] }} by mauto 4.
    assert {{ Γ, B ⊢ refl B[Wk] #0 : (Eq B[Wk][Wk] #1 #0)[Id,,#0] }} by mauto 4.
    assert {{ Γ, B ⊢s Id,,#0,,refl B'[Wk] #0 : Γ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0 }} by mauto 4.
    assert {{ Γ, B ⊢s Id,,#0,,refl B[Wk] #0 : Γ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0 }} by mauto 4.

    assert {{ Γ, B ⊢s Id,,#0,,refl B[Wk] #0 ≈ Id,,#0,,refl B'[Wk] #0 : Γ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0 }}
      by (econstructor; mauto 4).

    assert {{ Γ, B ⊢ C[Id,,#0,,refl B[Wk] #0] ≈ C'[Id,,#0,,refl B'[Wk] #0] : Type@j }}.
    {
      etransitivity;
        [eapply exp_eq_sub_cong_typ2' |
          eapply exp_eq_sub_cong_typ1];
        mauto 3.
    }

    assert {{ Γ ⊢ M1 ≈ M1' : B[Id] }} by (eapply wf_exp_eq_conv; mauto 3).
    assert {{ Γ ⊢s Id,,M1 ≈ Id,,M1' : Γ, B }} by mauto 3.
    assert {{ Γ ⊢ M2 ≈ M2' : B[Wk][Id,,M1] }} by (eapply wf_exp_eq_conv; mauto 3).
    assert {{ Γ ⊢s Id,,M1,,M2 ≈ Id,,M1',,M2' : Γ, B, B[Wk] }} by mauto 3.

    assert {{ Γ ⊢ (Eq B[Wk][Wk] #1 #0)[Id,,M1,,M2] ≈ Eq B M1 M2 : Type@i }}.
    {
      etransitivity;
        econstructor; mauto 3.
    }
    assert {{ Γ ⊢s Id,,M1,,M2,,L ≈ Id,,M1',,M2',,L' : Γ, B, B[Wk], Eq (B[Wk][Wk]) #1 #0 }}
      by (econstructor; mauto 4).

    assert {{ Γ ⊢s Id ,, M1' : Γ, B}} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,M1'] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,M1')]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢ M2' : B[Wk][Id,,M1'] }} by mauto 4.
    assert {{ Γ ⊢s Id,,M1',,M2' : Γ, B, B[Wk]}} by mauto 3.

    assert {{ Γ ⊢ (Eq B[Wk][Wk] #1 #0)[Id,,M1',,M2'] ≈ Eq B M1 M2 : Type@i }}.
    {
      etransitivity;
        [eapply exp_eq_sub_cong_typ2' | ];
        cycle 1.
      - eauto.
      - symmetry. eauto.
      - eauto.
      - eauto.
    }
    assert {{ Γ ⊢ L' : (Eq B[Wk][Wk] #1 #0)[Id,,M1',,M2'] }} by mauto 4.
    assert {{ Γ ⊢s Id,,M1',,M2',,L' : ((Γ, B), B[Wk]), Eq B[Wk][Wk] #1 #0 }} by mauto 3.

    eapply wf_conv;
      [econstructor; mauto 3 | mauto 2 | ].
    + eapply ctxeq_exp; eauto.
      eapply wf_conv;
        mauto 2.
    + etransitivity;
        [eapply exp_eq_sub_cong_typ2' |
          eapply exp_eq_sub_cong_typ1];
        mauto 3.

  - eexists.
    eapply exp_sub_typ; mauto 2.
    assert {{ Γ ⊢s Id ,, M1 : Γ, B}} by mauto 4.
    assert {{ Γ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,M1] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,M1)]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, M1 ,, M2 : Γ, B , B[Wk]}}.
    {
      econstructor; mauto 3.
      eapply wf_conv; mauto 2.
    }
    assert {{ Γ ⊢ B[Wk][Wk][Id ,, M1 ,, M2] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id ,, M1 ,, M2)]}}};
        [| transitivity {{{B[Wk][Id ,, M1]}}}];
        mauto 4.
      eapply exp_eq_sub_cong_typ2'; mauto 4.
      eapply wf_sub_eq_p_extend; mauto 4.
    }
    assert {{ Γ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ L : (Eq (B[Wk][Wk]) #1 #0) [ Id ,, M1 ,, M2]}}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var1 with (B:=B) | |];
            mauto 4.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var0 with (B:=B) | |];
            mauto 4.
    }
    mauto 3.

  - assert {{ Γ ⊢s Id ,, N : Γ, B}} by mauto 4.
    assert {{ Γ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,N] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,N)]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, N ,, N : Γ, B , B[Wk]}}.
    {
      econstructor; mauto 3.
      eapply wf_conv; mauto 2.
    }
    assert {{ Γ ⊢ B[Wk][Wk][Id ,, N ,, N] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id ,, N ,, N)]}}};
        [| transitivity {{{B[Wk][Id ,, N]}}}];
        mauto 4.
      eapply exp_eq_sub_cong_typ2'; mauto 4.
      eapply wf_sub_eq_p_extend; mauto 4.
    }
    assert {{ Γ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ refl B N : Eq B N N}} by mauto 3.
    assert {{ Γ ⊢ refl B N : (Eq (B[Wk][Wk]) #1 #0) [ Id ,, N ,, N]}}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var1 with (B:=B) | |];
            mauto 4.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var0 with (B:=B) | |];
            mauto 4.
    }
    assert {{Γ, B ⊢s Id,, #0 : Γ, B, B[Wk] }} by mauto 3.

    eapply wf_conv; mauto 3.
    etransitivity.
    + eapply exp_eq_sub_compose_typ; mauto 2.
      admit.
    + symmetry.
      eapply exp_eq_sub_cong_typ2'; mauto 2.
      symmetry.
      admit.

  - eexists.
    eapply exp_sub_typ; mauto 2.
    assert {{ Γ ⊢s Id ,, N : Γ, B}} by mauto 4.
    assert {{ Γ , B ⊢ B[Wk] : Type@i }} by mauto 4.
    assert {{ Γ , B , B[Wk] ⊢ B[Wk][Wk] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ B[Wk][Id,,N] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk ∘ (Id,,N)]}}};
        [| transitivity {{{B[Id]}}}];
        mauto 3.
      eapply exp_eq_sub_cong_typ2'; mauto 3.
    }
    assert {{ Γ ⊢s Id ,, N ,, N : Γ, B , B[Wk]}}.
    {
      econstructor; mauto 3.
      eapply wf_conv; mauto 2.
    }
    assert {{ Γ ⊢ B[Wk][Wk][Id ,, N ,, N] ≈ B : Type@i }}.
    {
      transitivity {{{B[Wk][Wk ∘ (Id ,, N ,, N)]}}};
        [| transitivity {{{B[Wk][Id ,, N]}}}];
        mauto 4.
      eapply exp_eq_sub_cong_typ2'; mauto 4.
      eapply wf_sub_eq_p_extend; mauto 4.
    }
    assert {{ Γ, B, B[Wk] ⊢ Eq (B[Wk][Wk]) # 1 # 0 : Type@i }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ refl B N : Eq B N N}} by mauto 3.
    assert {{ Γ ⊢ refl B N : (Eq (B[Wk][Wk]) #1 #0) [ Id ,, N ,, N]}}.
    {
      eapply wf_conv; mauto 2.
      symmetry.
      etransitivity.
      - eapply wf_exp_eq_eq_sub; mauto.
      - econstructor; mauto 3.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var1 with (B:=B) | |];
            mauto 4.
        + eapply wf_exp_eq_conv;
            [eapply id_sub_lookup_var0 with (B:=B) | |];
            mauto 4.
    }
    mauto 3.

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

  (** presup_sub_eq cases *)
  - econstructor...

  - assert {{ Γ ⊢ B[σ] ≈ B[σ'] : Type@i }} by mauto 4.
    eapply wf_conv...

  - assert {{ Γ ⊢ N'[Id] : A[Id] }}...

  - assert {{ Γ ⊢ N[σ][τ] : B[σ][τ] }} by mauto 4.
    eapply wf_conv...

  - econstructor...

  - econstructor; mauto 4.
    eapply wf_conv...

  - mauto.

  - assert (exists i, {{ Γ0 ⊢ A : Type@i }}) as [] by mauto.
    assert {{ Γ ⊢ #0[σ] : A[Wk][σ] }} by mauto 4.
    enough {{ Γ ⊢ #0[σ] : A[Wk∘σ] }} by mauto 4.
    eapply wf_conv...

  (** presup_subtyp cases *)
  - exists (max i i0); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - exists (max (S i) (S j)); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
  - mauto.
Admitted.
(* Qed. *)

Ltac gen_presup H := gen_presup_IH @presup_exp @presup_exp_eq @presup_sub_eq @presup_subtyp H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; clear_dups.
