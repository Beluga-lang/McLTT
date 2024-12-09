From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations.


Lemma glu_rel_eq : forall Γ A i M N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ Eq A M N : Type@i }}.
Proof.
Admitted.

#[export]
  Hint Resolve glu_rel_eq : mctt.

Lemma glu_rel_eq_refl : forall Γ A i M,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ refl A M : Eq A M M }}.
Proof.
Admitted.

#[export]
  Hint Resolve glu_rel_eq_refl : mctt.


Lemma glu_rel_eq_eqrec : forall Γ A i M1 M2 B j BR N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M1 : A }} ->
    {{ Γ ⊩ M2 : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊩ B : Type@j }} ->
    {{ Γ, A ⊩ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊩ N : Eq A M1 M2 }} ->
    {{ Γ ⊩ eqrec N as Eq A M1 M2 return B | refl -> BR end : B[Id,,M1,,M2,,N] }}.
Admitted.

#[export]
  Hint Resolve glu_rel_eq_eqrec : mctt.
