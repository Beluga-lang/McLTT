Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.Domain.
Require Import Mcltt.Evaluation.
Require Import Mcltt.Readback.
Require Import Coq.Relations.Relations.
Require Import Unicode.Utf8.

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

Inductive per_neu_univ (i : nat) : Ty :=
| per_neu_univ_ne : `(c ≈ c' ∈ Bot -> per_neu_univ (↑ (d_typ i) c) (↑ (d_typ i) c'))
.

Record pi_RT (T T' : exp) (p p' : Env) (R : Ty) : Set := mk_pi_rt
  {
    val_t : D 
  ; val_t' : D
  ; eval_t : ⟦ T ⟧ p ↘ val_t
  ; eval_t' : ⟦ T' ⟧ p ↘ val_t
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





  
Section PERDef.

  Variable i : nat.
  Variable Univ : ∀ j, j < i -> Ty.

  Inductive InterpUniv (d : D) (R : Ty) : Prop :=
  | iu_ne : `( j < i ->
               de ≈ de ∈ per_neu  ->
               InterpUniv (↑ (d_typ j) d) per_neu)
  | iu_nat : InterpUniv d_nat per_nat
  | iu_pi : `(InterpUniv DA PA ->
              ProperPerProd PA PF ->
              (∀ a PB DB, a ≈ a ∈ PA -> DF ∙d a ↘ DB -> PF a PB -> InterpUniv DB PB) ->
              (∀ a, a ≈ a ∈ PA -> ∃ DB, DF ∙d a ↘ DB) ->
              InterpUniv (d_pi DA DF) (RelProd PA PF))
  | iu_typ : 
  

  Inductive per_U : Ty :=
  | per_ne : `(C ≈ C' ∈ Bot -> ↑ A C ≈ ↑ A C' ∈ per_U)
  | per_nat : `(d_nat ≈ d_nat ∈ per_U)
  | per_univ : `(j < i -> j = j' -> d_typ j ≈ d_typ j' ∈ per_U)
  | per_pi : `(DA ≈ DA ∈ per_U ->
               InterpUniv DA PA ->
               (∀ a, a ≈ a ∈ PA -> ∃ DB, DF ∙d a ↘ DB) ->
               (∀ a, a ≈ a ∈ PA -> ∃ DB', DF' ∙d a ↘ DB') ->
               (InterpUniv DA P -> a0 ≈ a1 ∈ P ->
                 DF ∙d a0 ↘ DB0 ->
                 DF' ∙d a1 ↘ DB1 ->
                 DB0 ≈ DB1 ∈ per_U) ->
               d_pi DA DF ≈ d_pi DA' DF' ∈ per_U)
                
  | per_pi (A A' : D) (iA : A ≈ A' ∈ per_U) : `(a ≈ a' ∈ El iA ->
                                                pi_rt T (p ↦ a) T' (p' ↦ a') per_U ->
                                                d_pi A T p ≈ d_pi A' T' p' ∈ per_U)
  with El (A B : D) (q : A ≈ B ∈ per_U) : Ty :=
    match q with
      | 

End PERDef.  
