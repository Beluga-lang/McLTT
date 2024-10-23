From Coq Require Import Morphisms_Relations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Completeness Require Import LogicalRelation UniverseCases.
From Mcltt.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma valid_exp_eq : forall {Γ i A M1 M2},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ Eq A M1 M2 : Type@i }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion [] [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; mauto 3.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve valid_exp_eq : mcltt.

Lemma rel_exp_eq_sub : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Γ ⊨ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}.
Proof.
  intros * [env_relΓ] [env_relΔ]%rel_exp_of_typ_inversion [] [].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve rel_exp_eq_sub : mcltt.

Lemma rel_exp_refl_sub : forall {Γ σ Δ i A M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Γ ⊨ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  intros * [env_relΓ] [env_relΔ]%rel_exp_of_typ_inversion [].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split; econstructor; mauto 3.
  - per_univ_elem_econstructor; mauto 3; try solve_refl.
    typeclasses eauto.
  - econstructor; intuition.
    + etransitivity; [| symmetry]; eauto.
    + etransitivity; [symmetry |]; eauto.
Qed.

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
  intros * [env_relΓ]
             [env_relΔ]%rel_exp_of_typ_inversion
             []
             []
             [env_relΔAAEq]%rel_exp_of_typ_inversion
             [env_relΔA]
             [].
  destruct_conjs.
  pose env_relΔ.
  pose env_relΔA.
  pose env_relΔAAEq.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_of env_relΔAAEq.
  rename tail_rel into env_relΔAA.
  invert_per_ctx_envs_of env_relΔAA.
  invert_per_ctx_envs_of env_relΔA.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  assert {{ Dom ρ1 ↦ m1 ≈ ρ0 ↦ m0 ∈ env_relΔA }} by (apply_relation_equivalence; mauto 3).
  (on_all_hyp: destruct_rel_by_assumption env_relΔA).
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert {{ Dom ρ1 ↦ m1 ↦ m2 ≈ ρ0 ↦ m0 ↦ m3 ∈ env_relΔAA }} by (apply_relation_equivalence; unshelve eexists; intuition).
  (on_all_hyp: destruct_rel_by_assumption env_relΔAA).
  simplify_evals.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  assert {{ Dom ρ1 ↦ m1 ↦ m2 ↦ m4 ≈ ρ0 ↦ m0 ↦ m3 ↦ m'2 ∈ env_relΔAAEq }} as HrelΔAAEq by (apply_relation_equivalence; unshelve eexists; intuition).
  apply_relation_equivalence.
  (on_all_hyp: fun H => directed destruct (H _ _ HrelΔAAEq) as []).
  destruct_conjs.
  match_by_head per_eq ltac:(fun H => destruct H).
  (* 2: { *)
  (*   eexists; split. *)
  (*   2: { *)
  (*     econstructor. *)
  (*     1-2: econstructor; mauto 3. *)
  (*     2: econstructor; econstructor. *)
  (*     2: do 4 (econstructor; mauto 3). *)
  (*     2: mauto 3. *)
  (*     2: econstructor; mauto 3. *)
  (*     6: econstructor. *)
  (*     all: mauto 3. *)
      
  (*   } *)
  (* } *)
  (* - assert {{ Dom ρ1 ↦ n ≈ ρ0 ↦ n' ∈ env_relΔA }} as HΔA by (apply_relation_equivalence; unshelve eexists; intuition). *)
  (*   apply_relation_equivalence. *)
  (*   (on_all_hyp: fun H => directed destruct (H _ _ HΔA) as [? [[] []]]). *)
  (*   simplify_evals. *)
  (*   eexists; split; econstructor; mauto 3. *)
  (*     try solve [do 3 (econstructor; mauto 3)]. *)
  (*   + do 3 (econstructor; mauto 3). *)
  (* - do 3 (econstructor; mauto 3). *)
  (*   mauto 3. *)
  (* - do 3 (econstructor; mauto 3). *)
  (* - do 2 (econstructor; mauto 3). *)
    
  (* match_by_head (per_ctx_env _ {{{ Δ, A, A[Wk] }}} {{{ Δ, A, A[Wk] }}}) (fun H => idtac H). *)
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
