Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.Domain.
Require Import Mcltt.Evaluation.
Require Import Mcltt.Readback.
Require Import Coq.Relations.Relations.
Require Import Relations.Relation_Definitions.
Require Import Classes.RelationClasses.
Require Import Unicode.Utf8.
Require Import Arith.
From Equations Require Import Equations.



Generalizable All Variables.

Notation "a ≈ b ∈ P" := (P a b) (at level 80). 
Notation "a ∈' P" := (P a a) (at level 80).
Notation "a ~ b ∈ P" := (P a b) (at level 80).

Definition Ty : Type := relation D.
Definition Ev : Type := relation Env.

Definition Bot (c c' : Dn) : Prop :=
  ∀ n, ∃ u : Ne, ((Re n -- c ↘ u) ∧ (Re n -- c' ↘ u)).

Definition Top (d d' : Df) : Prop :=
  ∀ n, ∃ w, (Rf n -- d ↘ w) ∧ (Rf n -- d' ↘ w).

Definition TopT (A B : D) : Prop :=
  ∀ n, ∃ W, (Rty n -- A ↘ W) ∧ (Rty n -- B ↘ W).

Inductive per_nat : Ty :=
| per_nat_ze : d_zero ≈ d_zero ∈ per_nat
| per_nat_succ : `(a ≈ b ∈ per_nat -> d_succ a ≈ d_succ b ∈ per_nat)
| per_nat_ne : `(c ≈ c' ∈ Bot -> ↑ d_nat c ≈ ↑ d_nat c' ∈ per_nat)
.

Inductive per_neu : Ty :=
| per_neu_ne : `(c ≈ c' ∈ Bot -> ↑ A c ≈ ↑ A c' ∈ per_neu)
.

Check per_neu.


Record pi_RT (T T' : exp) (p p' : Env) (R : Ty) : Set := mk_pi_rt
  {
    val_t : D 
  ; val_t' : D
  ; eval_t : ⟦ T ⟧ p ↘ val_t
  ; eval_t' : ⟦ T' ⟧ p' ↘ val_t'
  ; eq_tt' : val_t ≈ val_t' ∈ R
  }.

Record pi_helper (f a f' a' : D) (R : Ty) : Set := mk_pi_helper
  {                                              
    fa : D
  ; fa' : D
  ; eval_fa : f ∙d a ↘ fa
  ; eval_fa': f ∙d a' ↘ fa'
  ; eq_fafa' : fa ≈ fa' ∈ R
  }.


(* ^^ This section copied directly from CPP18 ^^ *)
  
Section PERDef.

  Variable i : nat.
  Variable Univ : ∀ j, j < i -> Ty.


 
  Inductive InterpUniv : D -> D -> Ty -> Prop :=
  | iu_ne : `( j < i ->
               de ≈ de' ∈ Bot  ->
               InterpUniv (↑ (d_typ j) de) (↑ (d_typ j) de') per_neu)
  | iu_nat : InterpUniv d_nat d_nat per_nat
  | iu_pi : `(
             InterpUniv a b U_ab ->
             a ≈ b ∈ U_ab ->
             pi_RT T T' (p ↦ a) (p' ↦ b) U_im ->
             InterpUniv (d_pi a T p) (d_pi b T' p') (λ f f',
                 ∃ fa fb, (f ∙d a ↘ fa) ∧ (f' ∙d b ↘ fb) ∧ (fa ≈ fb ∈ U_im)
               )
              ) 
  | iu_univ : (∀ j (p : j < i),
                InterpUniv (d_typ j) (d_typ j) (Univ j (p)))
  .
  (* Need another case for universe, maybe needs to be mutual with per_U *)


  Inductive per_U : Ty :=
  | per_u_ne : `(C ≈ C' ∈ Bot -> ↑ A C ≈ ↑ A C' ∈ per_U)
  | per_u_nat : `(d_nat ≈ d_nat ∈ per_U)
  | per_u_univ : `(j < i -> j = j' -> d_typ j ≈ d_typ j' ∈ per_U)
  | per_u_pi : `(
               A ≈ A' ∈ per_U ->
               InterpUniv A A' per_A ->
               a ≈ a' ∈ per_A ->
               pi_RT T T' (p ↦ a) (p' ↦ a') per_U ->
               d_pi A T p ≈ d_pi A' T' p' ∈ per_U
               )   
  . 
End PERDef.

Check lt.

Equations? per_U_wf (i j : nat) : j < i -> Ty by wf (j) (lt) :=
  per_U_wf (n) (m) (p) := per_U m (λ k p', per_U_wf (n) k (lt_trans k m n  p' p)).
Proof.
Admitted.



  
