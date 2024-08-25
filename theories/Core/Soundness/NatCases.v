From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import ContextCases LogicalRelation Realizability SubstitutionCases TermStructureCases UniverseCases.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_nat : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ ℕ : Type@i }}.
Proof.
  intros * [Sb].
  assert {{ ⊢ Γ }} by mauto.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem.
    apply_predicate_equivalence.
    cbn.
    mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mcltt.

Lemma glu_rel_exp_of_nat : forall {Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat Δ {{{ M[σ] }}} m) ->
    {{ Γ ⊩ M : ℕ }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  exists 0.
  intros.
  edestruct Hbody as [? []]; mauto.
  econstructor; mauto.
  - glu_univ_elem_econstructor; mauto; reflexivity.
  - simpl; split; mauto 3.
Qed.

Lemma glu_rel_exp_zero : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ zero : ℕ }}.
Proof.
  intros * [Sb].
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  eexists; split; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcltt.

Lemma glu_rel_exp_succ : forall {Γ M},
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ succ M : ℕ }}.
Proof.
  intros * HM.
  assert {{ Γ ⊢ M : ℕ }} by mauto.
  cbn in HM.
  destruct_conjs.
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbn in *.
  destruct_conjs.
  eexists; split; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mcltt.

Lemma glu_rel_exp_natrec : forall {Γ i A MZ MS M},
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  intros * HA HMZ HMS HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@i }} by mauto 3.
  invert_glu_rel_exp HM.
  (* assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3. *)
  (* assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3. *)
  (* assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 3. *)
  (* assert {{ Γ ⊢ M : ℕ }} by mauto 3. *)
  (* pose proof HMZ as [] *)
  (* assert {{ ⊩ Γ }} by (econstructor; mauto 3). *)
  (* assert {{ Γ ⊩ zero : ℕ }} by mauto. *)
  (* assert {{ Γ ⊩ A[Id,,zero] : Type@i }}  *)
  (* invert_glu_rel_exp HMZ. *)
  (* rename x into *)
  (* assert {{ ⊩ Γ }} by (econstructor; mauto 2). *)
  (* assert {{ Γ ⊩ ℕ : Type@jMZ }} as Hℕ by mauto 3. *)
  (* assert {{ ⊩ Γ, ℕ }} by mauto 3. *)
  (* pose (SbΓℕ := cons_glu_sub_pred jMZ Γ {{{ ℕ }}} SbΓ). *)
  (* assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity). *)
  (* clear Hℕ. *)
  (* invert_glu_rel_exp HA. *)
  (* rename x into k. *)
  (* pose (SbΓℕA := cons_glu_sub_pred i {{{ Γ, ℕ }}} A SbΓℕ). *)
  (* assert {{ EG Γ, ℕ, A ∈ glu_ctx_env ↘ SbΓℕA }} by (econstructor; mauto 3; try reflexivity). *)
  (* invert_glu_rel_exp HMS. *)
  (* rename x into jMS. *)
  (* invert_glu_rel_exp HM. *)
  (* rename x into jM. *)
  (* assert {{ Γ ⊨ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} as [env_relΓ] by mauto using completeness_fundamental_exp. *)
  (* destruct_conjs. *)
  (* eexists; split; mauto. *)
  (* eexists. *)
  (* intros. *)
  (* assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption). *)
  (* destruct_glu_rel_exp_sub. *)
  (* (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
  (* destruct_by_head rel_typ. *)
  (* destruct_by_head rel_exp. *)
  (* simplify_evals. *)
  (* match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H). *)
  (* apply_predicate_equivalence. *)
  (* dir_inversion_clear_by_head nat_glu_exp_pred. *)
  (* rename p'0 into p. *)
  (* rename m0 into mz. *)
  (* rename a1 into am. *)
  (* rename a0 into az. *)
  (* rename m1 into r. *)
  (* eapply mk_glu_rel_exp_sub''; mauto 3. *)
  (* intros. *)
  (* This part requires a separate lemma for a clean induction *)
Admitted.

(* Goal forall {i Γ SbΓ A MZ MS}, *)
(*     {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} -> *)
(*     {{ Γ, ℕ ⊩ A : Type@i }} -> *)
(*     {{ Γ ⊩ MZ : A[Id,,zero] }} -> *)
(*     {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*     forall {Δ M m}, *)
(*       glu_nat Δ M m -> *)
(*       forall {σ p am P El r}, *)
(*         {{ Δ ⊢s σ ® p ∈ SbΓ }} -> *)
(*         {{ ⟦ A ⟧ p ↦ m ↘ am }} -> *)
(*         {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} -> *)
(*         {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} -> *)
(*         {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}. *)
(* Proof. *)
  (* intros * ? HA HMZ HMS. *)
  (* (* common things *) *)
  (* assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3. *)
  (* assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3. *)
  (* assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 3. *)
  (* invert_glu_rel_exp HMZ. *)
  (* assert {{ Γ ⊩ ℕ : Type@jMZ }} as Hℕ by mauto 3. *)
  (* assert {{ ⊩ Γ, ℕ }} by mauto 3. *)
  
  (* induction 1; intros; rename m into M; rename Γ0 into Δ. *)
  (* - (* glu_nat_zero *) *)
  (*   match_by_head eval_natrec ltac:(fun H => directed inversion H; subst; clear H). *)
  (*   destruct_by_head glu_rel_exp_sub. *)
  (*   simplify_evals. *)
  (*   handle_functional_glu_univ_elem. *)
  (*   assert {{ Δ ⊢ A[σ,,M] ≈ A[Id,,zero][σ] : Type@i }} as -> by admit. *)
  (*   assert *)
  (*     {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MZ[σ] : A[Id,,zero][σ] }} as -> by admit. *)
  (*   eassumption. *)
  (* - (* glu_nat_succ *) *)
  (*   rename m' into M'. *)
  (*   rename a into m'. *)
  (*   match_by_head eval_natrec ltac:(fun H => directed inversion H; subst; clear H). *)
  (*   destruct_by_head glu_rel_exp_sub. *)
  (*   simplify_evals. *)
  (*   handle_functional_glu_univ_elem. *)
  (*   (* assert {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,, M'] ® r0 ∈ ? }} by admit. *) *)
  (*   admit. *)
  (* - (* glu_nat_neut *) *)
  (*   admit. *)

#[export]
Hint Resolve glu_rel_exp_natrec : mcltt.
