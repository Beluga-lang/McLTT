Require Import Unicode.Utf8_core.

Require Import LibTactics.
Require Import Syntactic.Syntax.
Require Import Syntactic.System.

Lemma ctx_decomp : forall {Γ T}, {{ ⊢ Γ , T }} -> {{ ⊢ Γ }} ∧ ∃ i, {{ Γ ⊢ T : Type@i }}.
Proof with mauto.
  intros * HTΓ.
  inversion HTΓ; subst...
Qed.

Lemma lift_tm_ge : forall {Γ T n m}, n <= m -> {{ Γ ⊢ T : Type@n }} -> {{ Γ ⊢ T : Type@m }}.
Proof with mauto.
  intros * Hnm HT.
  induction m; inversion Hnm; subst...
Qed.

#[export]
Hint Resolve lift_tm_ge : mcltt.

Lemma lift_tm_max_left : forall {Γ T n} m, {{ Γ ⊢ T : Type@n }} -> {{ Γ ⊢ T : Type@(max n m) }}.
Proof with mauto.
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_tm_max_right : forall {Γ T} n {m}, {{ Γ ⊢ T : Type@m }} -> {{ Γ ⊢ T : Type@(max n m) }}.
Proof with mauto.
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma lift_eq_ge : forall {Γ T T' n m}, n <= m -> {{ Γ ⊢ T ≈ T': Type@n }} -> {{ Γ ⊢ T ≈ T' : Type@m }}.
Proof with mauto.
  intros * Hnm HTT'.
  induction m; inversion Hnm; subst...
Qed.

#[export]
Hint Resolve lift_eq_ge : mcltt.

Lemma lift_eq_max_left : forall {Γ T T' n} m, {{ Γ ⊢ T ≈ T' : Type@n }} -> {{ Γ ⊢ T ≈ T' : Type@(max n m) }}.
Proof with mauto.
  intros.
  assert (n <= max n m) by lia...
Qed.

Lemma lift_eq_max_right : forall {Γ T T'} n {m}, {{ Γ ⊢ T ≈ T' : Type@m }} -> {{ Γ ⊢ T ≈ T' : Type@(max n m) }}.
Proof with mauto.
  intros.
  assert (m <= max n m) by lia...
Qed.

(* Corresponds to presup-⊢≈ in the Agda proof *)
Lemma presup_ctx_eq : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} ∧ {{ ⊢ Δ }}.
Proof with mauto.
  intros * HΓΔ.
  induction HΓΔ as [|* ? [? ?]]...
Qed.

(* Corresponds to ≈-refl in the Agda code *)
Lemma tm_eq_refl : forall {Γ t T}, {{ Γ ⊢ t : T }} -> {{ Γ ⊢ t ≈ t : T }}.
Proof.
  mauto.
Qed.

Lemma sb_eq_refl : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve ctx_decomp presup_ctx_eq tm_eq_refl sb_eq_refl : mcltt.

(* Corresponds to t[σ]-Se in the Agda proof *)
Lemma exp_sub_typ : forall {Δ Γ T σ i}, {{ Δ ⊢ T : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ T[σ] : Type@i }}.
Proof.
  mauto.
Qed.

(* Corresponds to []-cong-Se′ in the Agda proof*)
Lemma eq_exp_sub_typ : forall {Δ Γ T T' σ i}, {{ Δ ⊢ T ≈ T' : Type@i }} -> {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢ T[σ] ≈ T'[σ] : Type@i }}.
Proof.
  mauto.
Qed.

#[export]
Hint Resolve exp_sub_typ eq_exp_sub_typ : mcltt.

(* Corresponds to ∈!⇒ty-wf in Agda proof *)
Lemma var_in_wf : forall {Γ T x}, {{ ⊢ Γ }} -> {{ #x : T ∈ Γ }} -> ∃ i, {{ Γ ⊢ T : Type@i }}.
Proof with mauto.
  intros * HΓ Hx. gen x T.
  induction HΓ; intros; inversion_clear Hx as [|? ? ? ? Hx']...
  destruct (IHHΓ _ _ Hx')...
Qed.

#[export]
Hint Resolve var_in_wf : mcltt.

Lemma presup_sb_ctx : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} ∧ {{ ⊢ Δ }}.
Proof with mauto.
  intros * Hσ.
  induction Hσ...
  - split; [|eapply ctx_decomp]...
  - destruct IHHσ1, IHHσ2...
  - destruct IHHσ...
  - destruct IHHσ; split...
    eapply proj2...
Qed.

#[export]
Hint Resolve presup_sb_ctx : mcltt.

Lemma presup_tm_ctx : forall {Γ t T}, {{ Γ ⊢ t : T }} -> {{ ⊢ Γ }}.
Proof with mauto.
  intros * Ht.
  induction Ht...
  eapply proj1...
Qed.

#[export]
Hint Resolve presup_tm_ctx : mcltt.

(* Corresponds to ∈!⇒ty≈ in Agda proof *)
Lemma var_in_eq : forall {Γ Δ T x}, {{ ⊢ Γ ≈ Δ }} -> {{ #x : T ∈ Γ }} -> ∃ S i, {{ #x : S ∈ Δ }} ∧ {{ Γ ⊢ T ≈ S : Type@i }} ∧ {{ Δ ⊢ T ≈ S : Type@i }}.
Proof with mauto.
  intros * HΓΔ Hx.
  gen Δ; induction Hx; intros; inversion_clear HΓΔ as [|? ? ? ? ? HΓΔ'].
  - do 2 eexists; repeat split...
  - destruct (IHHx _ HΓΔ') as [? [? [? [? ?]]]].
    do 2 eexists; repeat split...
Qed.

(* Corresponds to ⊢≈-sym in Agda proof *)
Lemma ctx_eq_sym : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof with mauto.
  intros.
  induction H...
Qed.

#[export]
Hint Resolve var_in_eq ctx_eq_sym : mcltt.

Lemma presup_sb_eq_ctx : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with mauto.
  intros.
  induction H; mauto; now (eapply proj1; mauto).
Qed.

#[export]
Hint Resolve presup_sb_eq_ctx : mcltt.

Lemma presup_tm_eq_ctx : forall {Γ t t' T}, {{ Γ ⊢ t ≈ t' : T }} -> {{ ⊢ Γ }}.
Proof with mauto.
  intros.
  induction H...
  Unshelve.
  constructor.
Qed.

#[export]
Hint Resolve presup_tm_eq_ctx : mcltt.
