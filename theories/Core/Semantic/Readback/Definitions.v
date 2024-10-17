From Mcltt.Core Require Import Base.
From Mcltt.Core.Semantic Require Import Evaluation.
From Mcltt.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "'Rnf' m 'in' s ↘ M" (in custom judg at level 80, m custom domain, s constr, M custom nf).
Reserved Notation "'Rne' m 'in' s ↘ M" (in custom judg at level 80, m custom domain, s constr, M custom nf).
Reserved Notation "'Rtyp' m 'in' s ↘ M" (in custom judg at level 80, m custom domain, s constr, M custom nf).

Generalizable All Variables.

Inductive read_nf : nat -> domain_nf -> nf -> Prop :=
| read_nf_type :
  `( {{ Rtyp a in s ↘ A }} ->
     {{ Rnf ⇓ 𝕌@i a in s ↘ A }} )
| read_nf_zero :
  `( {{ Rnf ⇓ ℕ zero in s ↘ zero }} )
| read_nf_succ :
  `( {{ Rnf ⇓ ℕ m in s ↘ M }} ->
     {{ Rnf ⇓ ℕ (succ m) in s ↘ succ M }} )
| read_nf_nat_neut :
  `( {{ Rne m in s ↘ M }} ->
     {{ Rnf ⇓ ℕ (⇑ ℕ m) in s ↘ ⇑ M }} )
| read_nf_fn :
  `( (** Normal form of arg type *)
     {{ Rtyp a in s ↘ A }} ->
     (** Normal form of eta-expanded body *)
     {{ $| m & ⇑! a s |↘ m' }} ->
     {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↘ b }} ->
     {{ Rnf ⇓ b m' in S s ↘ M }} ->

     {{ Rnf ⇓ (Π a ρ B) m in s ↘ λ A M }} )
| read_nf_refl :
  `( {{ Rtyp a in s ↘ A }} ->
     {{ Rnf ⇓ a m' in s ↘ M' }} ->
     {{ Rnf ⇓ (Eq a m1 m2) (refl a' m') in s ↘ refl A M' }} )
| read_nf_eq_neut :
  `( {{ Rne n in s ↘ N }} ->
     {{ Rnf ⇓ (Eq a m1 m2) (⇑ b n) in s ↘ ⇑ N }} )
| read_nf_neut :
  `( {{ Rne m in s ↘ M }} ->
     {{ Rnf ⇓ (⇑ a b) (⇑ c m) in s ↘ ⇑ M }} )
where "'Rnf' m 'in' s ↘ M" := (read_nf s m M) (in custom judg) : type_scope
with read_ne : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( {{ Rne !x in s ↘ #(s - x - 1) }} )
| read_ne_natrec :
  `( (** Normal form of motive *)
     {{ ⟦ B ⟧ ρ ↦ ⇑! ℕ s ↘ b }} ->
     {{ Rtyp b in S s ↘ B' }} ->

     (** Normal form of mz *)
     {{ ⟦ B ⟧ ρ ↦ zero ↘ bz }} ->
     {{ Rnf ⇓ bz mz in s ↘ MZ }} ->

     (** Normal form of MS *)
     {{ ⟦ B ⟧ ρ ↦ succ (⇑! ℕ s) ↘ bs }} ->
     {{ ⟦ MS ⟧ ρ ↦ ⇑! ℕ s ↦ ⇑! b (S s) ↘ ms }} ->
     {{ Rnf ⇓ bs ms in S (S s) ↘ MS' }} ->

     (** Neutral form of m *)
     {{ Rne m in s ↘ M }} ->

     {{ Rne rec m under ρ return B | zero -> mz | succ -> MS end in s ↘ rec M return B' | zero -> MZ | succ -> MS' end }} )
| read_ne_app :
  `( {{ Rne m in s ↘ M }} ->
     {{ Rnf n in s ↘ N }} ->
     {{ Rne m n in s ↘ M N }} )
| read_ne_eqrec :
  `( (** Normal form of type annotation *)
     {{ Rtyp a in s ↘ A }} ->
     {{ Rnf ⇓ a m1 in s ↘ M1 }} ->
     {{ Rnf ⇓ a m2 in s ↘ M2 }} ->

     (** Normal form of motive *)
     {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) ↘ b }} ->
     {{ Rtyp b in S (S (S s)) ↘ B' }} ->

     (** Normal form of BR *)
     {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↦ ⇑! a s ↦ refl a (⇑! a s) ↘ bbr }} ->
     {{ ⟦ BR ⟧ ρ ↦ ⇑! a s ↘ br }} ->
     {{ Rnf ⇓ bbr br in S s ↘ BR' }} ->

     (** Neutral form of m *)
     {{ Rne n in s ↘ N }} ->

     {{ Rne eqrec n under ρ as Eq a m1 m2 return B | refl -> BR end in s ↘ eqrec N as Eq A M1 M2 return B' | refl -> BR' end }} )
where "'Rne' m 'in' s ↘ M" := (read_ne s m M) (in custom judg) : type_scope
with read_typ : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( {{ Rtyp 𝕌@i in s ↘ Type@i }} )
| read_typ_nat :
  `( {{ Rtyp ℕ in s ↘ ℕ }} )
| read_typ_pi :
  `( (** Normal form of arg type *)
     {{ Rtyp a in s ↘ A }} ->

     (** Normal form of ret type *)
     {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↘ b }} ->
     {{ Rtyp b in S s ↘ B' }} ->

     {{ Rtyp Π a ρ B in s ↘ Π A B' }})
| read_typ_eq :
  `( (** Normal form of equality type *)
     {{ Rtyp a in s ↘ A }} ->

     (** Normal form of LHS *)
     {{ Rnf ⇓ a m1 in s ↘ M1 }} ->

     (** Normal form of RHS *)
     {{ Rnf ⇓ a m2 in s ↘ M2 }} ->

     {{ Rtyp Eq a m1 m2 in s ↘ Eq A M1 M2 }})
| read_typ_neut :
  `( {{ Rne b in s ↘ B }} ->
     {{ Rtyp ⇑ a b in s ↘ ⇑ B }})
where "'Rtyp' m 'in' s ↘ M" := (read_typ s m M) (in custom judg) : type_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ : mcltt.
