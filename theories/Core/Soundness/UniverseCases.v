From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation Realizability.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_exp_of_typ : forall {Γ Sb A i},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Type@i }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_univ i }} /\
              forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ A[σ] ® P }}) ->
    {{ Γ ⊩ A : Type@i }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  exists (S i).
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.

Lemma glu_rel_exp_typ : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ Type@i : Type@(S i) }}.
Proof.
  intros * [Sb].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbv.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_typ : mcltt.
