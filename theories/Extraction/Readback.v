From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Readback Evaluation ExpNoConfusion.
From Mcltt.Extraction Require Import Evaluation.
From Equations Require Import Equations.
Import Domain_Notations.

Generalizable All Variables.

Inductive read_nf_order : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order s a ->
    read_nf_order s d{{{ ⇓ 𝕌@i a }}} )
| rnf_zero :
  `( read_nf_order s d{{{ ⇓ ℕ zero }}} )
| rnf_succ :
  `( read_nf_order s d{{{ ⇓ ℕ m }}} ->
     read_nf_order s d{{{ ⇓ ℕ (succ m) }}} )
| rnf_nat_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ ℕ (⇑ ℕ m) }}} )
| rnf_fn :
  `( read_typ_order s a ->
     (forall m' b,
         {{ $| m & ⇑! a s |↘ m' }} ->
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_nf_order (S s) d{{{ ⇓ b m' }}}) ->
     read_nf_order s d{{{ ⇓ (Π a p B) m }}} )
| rnf_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ (⇑ a b) (⇑ c m) }}} )

with read_ne_order : nat -> domain_ne -> Prop :=
| rne_var :
  `( read_ne_order s d{{{ !x }}} )
| rne_app :
  `( read_ne_order s m ->
     read_nf_order s n ->
     read_ne_order s d{{{ m n }}} )
| rne_natrec :
  `( (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         read_typ_order (S s) b) ->
     (forall bz,
         {{ ⟦ B ⟧ p ↦ zero ↘ bz }} ->
         read_nf_order s d{{{ ⇓ bz mz }}}) ->
     (forall b bs ms,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         {{ ⟦ B ⟧ p ↦ succ (⇑! ℕ s) ↘ bs }} ->
         {{ ⟦ MS ⟧ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) ↘ ms }} ->
         read_nf_order (S (S s)) d{{{ ⇓ bs ms }}}) ->
     read_ne_order s m ->
     read_ne_order s d{{{ rec m under p return B | zero -> mz | succ -> MS end }}} )

with read_typ_order : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order s d{{{ 𝕌@i }}} )
| rtyp_nat :
  `( read_typ_order s d{{{ ℕ }}} )
| rtyp_pi :
  `( read_typ_order s a ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_typ_order (S s) b) ->
     read_typ_order s d{{{ Π a p B }}})
| rtyp_neut :
  `( read_ne_order s b ->
    read_typ_order s d{{{ ⇑ a b }}} ).

#[local]
  Hint Constructors read_nf_order read_ne_order read_typ_order : mcltt.


Lemma read_nf_order_sound : forall s d m,
    {{ Rnf d in s ↘ m }} ->
    read_nf_order s d
with read_ne_order_sound : forall s d m,
    {{ Rne d in s ↘ m }} ->
    read_ne_order s d
with read_typ_order_sound : forall s d m,
    {{ Rtyp d in s ↘ m }} ->
    read_typ_order s d.
Proof  with (econstructor; intros; functional_eval_rewrite_clear; eauto).
  - clear read_nf_order_sound; induction 1...
  - clear read_ne_order_sound; induction 1...
  - clear read_typ_order_sound; induction 1...
Qed.

#[local]
  Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound : mcltt.

Derive Signature for read_nf_order read_ne_order read_typ_order.
