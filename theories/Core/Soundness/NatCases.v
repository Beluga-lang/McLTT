From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_nat : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ ℕ : Type@i }}.
Proof.
  intros * [Sb].
  assert {{ ⊢ Γ }} by mauto.
  eexists; split; mauto.
  exists (S i).
  intros.
  econstructor; mauto.
  repeat split; mauto 4.
  do 2 eexists; split.
  - glu_univ_elem_econstructor; mauto; reflexivity.
  - simpl. mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mcltt.

Lemma glu_rel_exp_zero : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ zero : ℕ }}.
Proof.
  intros * [Sb].
  assert {{ ⊢ Γ }} by mauto.
  eexists; split; mauto.
  exists 1.
  intros.
  econstructor; mauto.
  - glu_univ_elem_econstructor; mauto; reflexivity.
  - split; mauto.
    simpl. mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcltt.

Lemma glu_rel_exp_succ : forall {Γ M},
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ succ M : ℕ }}.
Proof.
  intros * HM.
  assert {{ Γ ⊢ M : ℕ }} by mauto.
  destruct HM as [Sb [? [i]]].
  destruct_conjs.
  eexists; split; mauto.
  exists i.
  intros.
  repeat match goal with
         | H: context[glu_rel_exp_sub _ _ _ _ _ _] |- _ =>
             match type of H with
             | __mark__ _ _ => fail 1
             | _ => edestruct H; [eassumption |]; mark H
             end
         end; unmark_all.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  simpl in *.
  destruct_conjs.
  econstructor; mauto.
  split; mauto 4.
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
