Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.Domain.
Require Import Mcltt.Evaluation.
Require Import Mcltt.Readback.
Require Import Coq.Relations.Relations.
Require Import Relations.Relation_Definitions.
Require Import Classes.RelationClasses.
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

(* vv This section copied directly from CPP18 vv *)
Definition binRelEq (D:Type) (R1:relation D) (R2:relation D) :=
  (forall x y, R1 x y <-> R2 x y).

(* this notation slightly modifiedd to inlude the type information *)
Notation "R1 =~ D ~= R2" := (binRelEq D R1 R2) (at level 75, no associativity).

Instance binRelEq_EQ (D:Type) : Equivalence (@binRelEq D).
Proof.
  constructor 1; red; intros; red; intros.
split; auto.
red in H.
split; auto; apply H.

red in H. red in H0.
split; auto; intro Z. 
apply H0; apply H; auto.
apply H; apply H0; auto.
Qed.  


Definition rel_oper (D:Type) := D -> relation D -> Prop.

Record ProperRelOper (A:relation D) (F:rel_oper D) :=
  Mk_ProperRelOper {
    ro_resp_arg: forall a0 a1 Y, a0 ≈ a1 ∈ A -> F a0 Y -> F a1 Y;
    ro_resp_ex:  forall a, a ≈ a ∈ A -> exists B, F a B;
    ro_resp_det: forall a0 a1 Y0 Y1, a0 ≈ a1 ∈ A -> F a0 Y0 -> F a1 Y1 -> (Y0 =~D~= Y1)
  }
.

Inductive RelProd (A:relation D) (F:rel_oper D) : relation D :=
| RelProd_intro: forall f0 f1,
  (forall a0 a1, a0 ≈ a1 ∈ A -> exists y0 y1 Y,
    F a0 Y /\ (f0 ∙d a0 ↘ y0) /\ (f1 ∙d a1 ↘ y1) /\ y0 ≈ y1 ∈ Y) ->
  f0 ≈ f1 ∈ RelProd A F
.

Record ProperPerProd (A:relation D) (F:rel_oper D) :=
  Mk_ProperPerOper {
    po_ro      :> ProperRelOper A F;
    po_per_codom: forall a Y, a ≈ a ∈ A -> F a Y -> PER Y;
    po_per_dom :> PER A
  }
.

(* ^^ This section copied directly from CPP18 ^^ *)
  
Section PERDef.

  Variable i : nat.
  Variable Univ : ∀ j, j < i -> Ty.


 
  Inductive InterpUniv : D -> Ty -> Prop :=
  | iu_ne : `( j < i ->
               de ≈ de ∈ Bot  ->
               InterpUniv (↑ (d_typ j) de) per_neu)
  | iu_nat : InterpUniv d_nat per_nat
  | iu_pi : `(InterpUniv DA PA ->
              ProperPerProd PA PF ->
              (∀ a PB DB, a ≈ a ∈ PA -> DF ∙d a ↘ DB -> PF a PB -> InterpUniv DB PB) ->
              (∀ a, a ≈ a ∈ PA -> ∃ DB, DF ∙d a ↘ DB) ->
              InterpUniv (d_pi DA DF) (RelProd PA PF)).
  


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
  . 
End PERDef.  
