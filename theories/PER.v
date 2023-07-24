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
  | iu_pi : `( A ≈ A' ∈ per_U ->
               InterpUniv A A' per_A ->
               (∀ a a', a ≈ a' ∈ per_A ->
                        pi_RT T T' (p ↦ a) (p' ↦ a') U_im
               ) ->
               InterpUniv (d_pi A T p) (d_pi A' T' p') (λ f f',
                   ∃ fa fa' : D , ∀ a a', a ≈ a' ∈ per_A ->
                    (f ∙d a ↘ fa) ∧ (f' ∙d b ↘ fb) ∧ (fa ≈ fb ∈ U_im)                  
                 )
               )  
  | iu_univ : (∀ j (p : j < i),
                InterpUniv (d_typ j) (d_typ j) (Univ j (p)))
  .


  Inductive per_U : Ty :=
  | per_u_ne : `(C ≈ C' ∈ Bot -> ↑ A C ≈ ↑ A C' ∈ per_U)
  | per_u_nat : `(d_nat ≈ d_nat ∈ per_U)
  | per_u_univ : `(j < i -> j = j' -> d_typ j ≈ d_typ j' ∈ per_U)
  | per_u_pi : `(
               A ≈ A' ∈ per_U ->
               InterpUniv A A' per_A ->
               (∀ a a', a ≈ a' ∈ per_A ->
               pi_RT T T' (p ↦ a) (p' ↦ a') per_U ->
               d_pi A T p ≈ d_pi A' T' p' ∈ per_U
               ))   
  . 
End PERDef.

Equations per_U_wf (i : nat) : Ty by wf (i) (lt) :=
  per_U_wf (i) := per_U (i) (λ k p, per_U_wf k)
.

Definition U_PER (i : nat) : Ty := per_U i (λ k p, per_U_wf k). 

Definition UniInterp (i : nat) : D -> D -> Ty -> Prop := InterpUniv i (λ k p, per_U_wf k).

Record RelTyp (i : nat) (T T' : exp) (p p' : Env) : Set := mk_rel_typ
  {
    val_T : D 
  ; val_T' : D
  ; eval_T : ⟦ T ⟧ p ↘ val_T
  ; eval_T' : ⟦ T' ⟧ p' ↘ val_T'
  ; eq_TT' : val_T ≈ val_T' ∈ U_PER i
  }.

(* Inductive ctx_equiv_PER : Ctx -> Ctx -> Prop :=
| ctx_empty : ctx_equiv_PER nil nil
| ctx_cong (Γ Δ : Ctx) (ctx_eq : ctx_equiv_PER Γ Δ) :
  `(
      (∀ p p',
          InterpCtx Γ Δ R ->
          p ≈ p' ∈ R ->
          RelTyp i T T' p p' 
      ) ->
      ctx_equiv_PER (T :: Γ) (T' :: Δ)        
    )
with InterpCtx : Ctx -> Ctx -> Ev -> Prop :=
| InterpEmp : InterpCtx nil nil (λ p p', True).
 | InterpCong : `(ctx_cong Γ Δ ctx_eq rel ->    
*)
