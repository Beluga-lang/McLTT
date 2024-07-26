(* From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses. *)

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.Corollaries.
From Mcltt.Core.Soundness Require Export LogicalRelation Weakening.
Import Domain_Notations.

Inductive glu_elem_bot Γ t T i c A : Prop :=
| glu_elem_bot_make : forall P El,
    {{ Γ ⊢ t : T }} ->
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    P Γ T ->
    per_bot c c ->
    (forall Δ σ w, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ w }} -> {{ Δ ⊢ t [ σ ] ≈ w : T [ σ ] }}) ->
    glu_elem_bot Γ t T i c A.
#[export]
  Hint Constructors glu_elem_bot : mcltt.


Inductive glu_elem_top Γ t T i a A : Prop :=
| glu_elem_top_make : forall P El,
    {{ Γ ⊢ t : T }} ->
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    P Γ T ->
    per_top d{{{ ⇓ A a }}} d{{{ ⇓ A a }}} ->
    (forall Δ σ w, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ A a in length Δ ↘ w }} -> {{ Δ ⊢ t [ σ ] ≈ w : T [ σ ] }}) ->
    glu_elem_top Γ t T i a A.
#[export]
  Hint Constructors glu_elem_top : mcltt.


Inductive glu_typ_top Γ T i A : Prop :=
| glu_typ_top_make :
    {{ Γ ⊢ T : Type@i }} ->
    per_top_typ A A ->
    (forall Δ σ W, {{ Δ ⊢w σ : Γ }} -> {{ Rtyp A in length Δ ↘ W }} -> {{ Δ ⊢ T [ σ ] ≈ W : Type@i }}) ->
    glu_typ_top Γ T i A.
#[export]
  Hint Constructors glu_typ_top : mcltt.


Theorem realize_glu_univ_elem_gen : forall A i P El,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    (forall Γ T, P Γ T -> glu_typ_top Γ T i A) /\
      (forall Γ t T c, glu_elem_bot Γ t T i c A -> El Γ t T d{{{ ⇑ A c }}}) /\
      (forall Γ t T a, El Γ t T a -> glu_elem_top Γ t T i a A).
Proof.
Admitted.
