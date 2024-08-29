From Mcltt Require Import Base LibTactics.
From Mcltt.Algorithmic Require Import Typing.Definitions.
From Mcltt.Algorithmic Require Export Subtyping.Lemmas.
From Mcltt.Core Require Import Soundness Completeness.
From Mcltt.Core.Completeness Require Import Consequences.Rules.
From Mcltt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

(* There might be a better file for this. *)
Lemma idempotent_nbe_ty : forall {Γ i A B C},
    {{ Γ ⊢ A : Type@i }} ->
    nbe_ty Γ A B ->
    nbe_ty Γ B C ->
    B = C.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ B : Type@i }} as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.

Lemma functional_alg_type_infer : forall {Γ A A' M},
    {{ Γ ⊢a M ⟹ A }} ->
    {{ Γ ⊢a M ⟹ A' }} ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    functional_nbe_rewrite_clear;
    f_equal;
    try reflexivity;
    intuition.
  - assert ({{{ Type@i }}} = {{{ Type@i0 }}}) as [= <-] by intuition.
    assert ({{{ Type@j }}} = {{{ Type@j0 }}}) as [= <-] by intuition.
    reflexivity.
  - assert ({{{ Π A B }}} = {{{ Π A0 B0 }}}) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (A = A0) as <- by mauto using functional_ctx_lookup.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

Lemma alg_type_sound :
  (forall {Γ A M}, {{ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} -> forall i, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }}) /\
    (forall {Γ A M}, {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}).
Proof.
  apply alg_type_mut_ind; intros; try mautosolve 4.
  - assert {{ Γ ⊢ M : A }} by mauto 3.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [j] by (gen_presups; eauto 2).
    assert {{ Γ ⊢ A : Type@(max i j) }} by mauto 3 using lift_exp_max_right.
    assert {{ Γ ⊢ B : Type@(max i j) }} by mauto 3 using lift_exp_max_left.
    assert {{ Γ ⊢ A ⊆ B }} by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 2.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, ℕ, A }} by mauto 3.
    assert {{ Γ ⊢ M : ℕ }} by mauto 2.
    assert {{ Γ ⊢ A[Id,,zero] : Type@i }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] ≈ B : Type@i }} as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 2 using soundness_ty'.
    assert {{ Γ, A ⊢ M : B }} by mauto 2.
    assert (exists j, {{ Γ, A ⊢ B : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert {{ Γ ⊢ Π A B ≈ Π C B : Type@(max i j) }} as <- by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ M : Π A B }} by mauto 2.
    assert (exists i, {{ Γ ⊢ Π A B : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N] ≈ C : Type@i }} as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - assert {{ Γ ⊢ #x : A }} by mauto 2.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 2.
    assert {{ Γ ⊢ A ≈ B : Type@i }} as <- by mauto 2 using soundness_ty'.
    mauto 3.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_normal : forall {Γ A A' M},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a M ⟹ A }} ->
    nbe_ty Γ A A' ->
    A = A'.
Proof.
  intros * ? Hinfer Hnbe. gen A'.
  assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - f_equiv; eapply idempotent_nbe_ty; revgoals; try eassumption.
    assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
    assert {{ Γ ⊢ M : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3 using alg_type_infer_sound.
    mauto 4.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 3 using soundness_ty'.
    assert {{ Γ, A ⊢ M : B }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert {{ ⊢ Γ, A ≈ Γ, ~(C : exp) }} by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env {{{ Γ, ~(C : exp) }}} d{{{ p ↦ ⇑! a (length Γ) }}}) by mauto 3.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C by mauto 3 using idempotent_nbe_ty.
    assert (nbe_ty {{{ Γ, A }}} B B').
    {
      assert (exists W, nbe {{{ Γ, A }}} B {{{ Type@j }}} W /\ nbe {{{ Γ, ~(C : exp) }}} B {{{ Type@j }}} W) as [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]] by mauto 3 using ctxeq_nbe_eq.
      assert (nbe_ty {{{ Γ, ~(C : exp) }}} B B') by mauto 3.
      functional_nbe_rewrite_clear.
      eassumption.
    }
    simpl.
    f_equiv.
    mauto 3.
  - assert {{ Γ ⊢ M : Π A B }} by mauto 3 using alg_type_infer_sound.
    assert (exists i, {{ Γ ⊢ Π A B : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ B[Id,,N] : Type@i }} by mauto 3.
    f_equiv.
    mauto 3 using idempotent_nbe_ty.
  - assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 2.
    f_equiv.
    mauto 3 using idempotent_nbe_ty.
Qed.

Lemma alg_type_check_type_implies_alg_type_infer_type : forall {Γ A i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a A ⟸ Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? ? ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? ? ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A0 with (A1 : exp) in * by (symmetry; mauto 3 using alg_type_infer_normal).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  firstorder.
Qed.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Π A B : Type@i }} ->
    {{ Γ ⊢a M ⟸ Π A B }} ->
    exists A' B', {{ Γ ⊢a M ⟹ Π A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}.
Proof.
  intros * ? ? Hcheck.
  assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 3.
  inversion Hcheck as [? ? ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? ? C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A0 with (A1 : exp) in * by (symmetry; mauto 3 using alg_type_infer_normal).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert {{ Γ ⊢ M : Π A2 B0 }} by mauto 3 using alg_type_infer_sound.
  assert (exists j, {{ Γ ⊢ Π A2 B0 : Type@j }}) as [j] by (gen_presups; eauto 2).
  assert ({{ Γ ⊢ A2 : Type@j }} /\ {{ Γ, ~(A2 : exp) ⊢ B0 : Type@j }}) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty Γ A A2) by mauto 3.
  assert {{ Γ ⊢ A ≈ A2 : Type@i }} by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env {{{ Γ, A }}} d{{{ p ↦ ⇑! a (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B B') by mauto 3.
  assert (initial_env {{{ Γ, ~(A2 : exp) }}} d{{{ p ↦ ⇑! a0 (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B0 B0).
  {
    assert {{ ⊢ Γ, A ≈ Γ, ~(A2 : exp) }} by mauto 3.
    assert {{ Γ, A ⊢ B0 : Type@j }} by mauto 3.
    assert (exists W, nbe {{{ Γ, A }}} B0 {{{ Type@j }}} W /\ nbe {{{ Γ, ~(A2 : exp) }}} B0 {{{ Type@j }}} W) as [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]] by mauto 3 using ctxeq_nbe_eq.
    assert (nbe_ty {{{ Γ, ~(A2 : exp) }}} B0 B0) by mauto 3.
    functional_nbe_rewrite_clear.
    eassumption.
  }
  mauto 3.
Qed.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  intros * [] **.
  assert {{ Γ0 ⊢a B ⊆ A' }} by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Lemma alg_type_check_conv : forall {Γ i A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  intros * [] **.
  assert {{ Γ0 ⊢ B ⊆ A' }} by mauto 3.
  assert {{ Γ0 ⊢a B ⊆ A' }} by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Lemma alg_type_complete : forall {Γ A M},
    (* There should be one more condition to rule out substitution cases *)
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
Proof.
  induction 1; gen_presups; mauto 4 using alg_subtyping_complete.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, {{ Γ, ℕ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3 using alg_type_check_type_implies_alg_type_infer_type.
    assert {{ Γ ⊢ A[Id,,M] : Type@i }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i }} as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3 using alg_type_check_type_implies_alg_type_infer_type.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3 using alg_type_check_type_implies_alg_type_infer_type.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3 using alg_type_check_type_implies_alg_type_infer_type.
    assert (exists B', {{ Γ, A ⊢a M ⟹ B' }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by mauto 3 using soundness_ty.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ, A ⊢ M : B' }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B' : Type@j }}) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert (exists A' B', {{ Γ ⊢a M ⟹ Π A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]]
        by mauto 3 using alg_type_check_pi_implies_alg_type_infer_pi.
    assert {{ Γ ⊢ M : Π A' B' }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ ⊢ Π A' B' : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A' : Type@j }} /\ {{ Γ, A' ⊢ B' : Type@j }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A' }} by mauto 3.
    assert {{ Γ ⊢ B'[Id,,N] : Type@j }} by mauto 3.
    assert (exists W, nbe_ty Γ {{{ B'[Id,,N] }}} W /\ {{ Γ ⊢ B'[Id,,N] ≈ W : Type@j }}) as [W []] by (eapply soundness_ty; mauto 3).
    assert {{ Γ, A ⊢ B' : Type@j }} by mauto 4.
    assert {{ Γ, A ⊢ B' ⊆ B }} by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert {{ Γ ⊢ B'[Id,,N] ⊆ B[Id,,N] }} by mauto 3.
    assert {{ Γ ⊢ W ⊆ B[Id,,N] }} by (transitivity {{{ B'[Id,,N] }}}; mauto 3).
    econstructor; mauto 4 using alg_type_check_conv, alg_subtyping_complete.
  - assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 3.
    assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - admit. (* This case should be ruled out *)
  - mauto using alg_type_check_subtyp.
  Fail idtac. (* Make sure there is no more goals *)
Admitted.
