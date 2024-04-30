From Mcltt Require Import Base.
From Mcltt Require Import Domain.
From Mcltt Require Import Evaluate.
From Mcltt Require Import Syntax.
From Mcltt Require Import System.

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
  (* Nf of arg type *)
  `( {{ Rtyp a in s ↘ A }} ->

     (* Nf of eta-expanded body *)
     {{ $| m & ⇑! a s |↘ m' }} ->
     {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
     {{ Rnf ⇓ b m' in S s ↘ M }} ->

     {{ Rnf ⇓ (Π a p B) m in s ↘ λ A M }} )
| read_nf_neut :
  `( {{ Rne m in s ↘ M }} ->
     {{ Rnf ⇓ (⇑ a b) (⇑ c m) in s ↘ ⇑ M }} )
where "'Rnf' m 'in' s ↘ M" := (read_nf s m M) (in custom judg) : exp_scope
with read_ne : nat -> domain_ne -> ne -> Prop :=
| read_ne_var :
  `( {{ Rne !x in s ↘ #(s - x - 1) }} )
| read_ne_app :
  `( {{ Rne m in s ↘ M }} ->
     {{ Rnf n in s ↘ N }} ->
     {{ Rne m n in s ↘ M N }} )
| read_ne_natrec :
  (* Nf of motive *)
  `( {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
     {{ Rtyp b in S s ↘ B' }} ->

     (* Nf of mz *)
     {{ ⟦ B ⟧ p ↦ zero ↘ bz }} ->
     {{ Rnf ⇓ bz mz in s ↘ MZ }} ->

     (* Nf of MS *)
     {{ ⟦ B ⟧ p ↦ succ (⇑! ℕ s) ↘ bs }} ->
     {{ ⟦ MS ⟧ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) ↘ ms }} ->
     {{ Rnf ⇓ bs ms in S (S s) ↘ MS' }} ->

     (* Ne of m *)
     {{ Rne m in s ↘ M }} ->

     {{ Rne rec m under p return B | zero -> mz | succ -> MS end in s ↘ rec M return B' | zero -> MZ | succ -> MS' end }} )
where "'Rne' m 'in' s ↘ M" := (read_ne s m M) (in custom judg) : exp_scope
with read_typ : nat -> domain -> nf -> Prop :=
| read_typ_univ :
  `( {{ Rtyp 𝕌@i in s ↘ Type@i }} )
| read_typ_nat :
  `( {{ Rtyp ℕ in s ↘ ℕ }} )
| read_typ_pi :
  (* Nf of arg type *)
  `( {{ Rtyp a in s ↘ A }} ->

     (* Nf of ret type *)
     {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
     {{ Rtyp b in S s ↘ B' }} ->

     {{ Rtyp Π a p B in s ↘ Π A B' }})
| read_typ_neut :
  `( {{ Rne b in s ↘ B }} ->
     {{ Rtyp ⇑ a b in s ↘ ⇑ B }})
where "'Rtyp' m 'in' s ↘ M" := (read_typ s m M) (in custom judg) : exp_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop.
