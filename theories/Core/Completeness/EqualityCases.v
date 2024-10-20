From Coq Require Import Morphisms_Relations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations.

Lemma valid_exp_eq : forall {Γ i A M1 M2},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ Eq A M1 M2 : Type@i }}.
Proof.
Admitted.
#[export]
Hint Resolve valid_exp_eq : mcltt.

Lemma rel_exp_eq_sub : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Γ ⊨ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eq_sub : mcltt.

Lemma rel_exp_refl_sub : forall {Γ σ Δ i A M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Γ ⊨ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_refl_sub : mcltt.

Lemma rel_exp_eqrec_sub : forall {Γ σ Δ i A M1 M2 j B BR N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Δ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ ⊨ N : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ]
         ≈ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end
        : B[σ,,M1[σ],,M2[σ],,N[σ]] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_sub : mcltt.

Lemma rel_exp_eq_cong : forall {Γ i A A' M1 M1' M2 M2'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ ⊨ Eq A M1 M2 ≈ Eq A' M1' M2' : Type@i }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eq_cong : mcltt.

Lemma rel_exp_refl_cong : forall {Γ i A A' M M'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ refl A M ≈ refl A' M' : Eq A M M }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_refl_cong : mcltt.

Lemma rel_exp_eqrec_cong : forall {Γ i A A' M1 M1' M2 M2' j B B' BR BR' N N'},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B ≈ B' : Type@j }} ->
    {{ Γ, A ⊨ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ N ≈ N' : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end
         ≈ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end
        : B[Id,,M1,,M2,,N] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_cong : mcltt.

Lemma rel_exp_eqrec_beta : forall {Γ i A M j B BR},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ eqrec refl A M as Eq A M M return B | refl -> BR end
         ≈ BR[Id,,M]
        : B[Id,,M,,M,,refl A M] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_beta : mcltt.
