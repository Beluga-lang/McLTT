From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability UniverseCases.
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
    cbv.
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
  cbv in HM.
  destruct_conjs.
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  destruct_glu_rel_exp_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbv in *.
  destruct_conjs.
  eexists; split; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mcltt.

Lemma glu_rel_exp_natrec : forall {Γ A i MZ MS M},
    {{ Γ , ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ , ℕ , A ⊩ MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Admitted.

#[export]
Hint Resolve glu_rel_exp_natrec : mcltt.
