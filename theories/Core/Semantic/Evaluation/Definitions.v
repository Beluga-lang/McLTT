From Mcltt Require Import Base.
From Mcltt Require Export Domain.
Import Domain_Notations.

Reserved Notation "'⟦' M '⟧' ρ '↘' r" (in custom judg at level 80, M custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" (in custom judg at level 80, m custom domain at level 99, A custom exp at level 99, MZ custom exp at level 99, MS custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'$|' m '&' n '|↘' r" (in custom judg at level 80, m custom domain at level 99, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'⟦' σ '⟧s' ρ '↘' ρσ" (in custom judg at level 80, σ custom exp at level 99, ρ custom domain at level 99, ρσ custom domain at level 99).

Generalizable All Variables.

Inductive eval_exp : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( {{ ⟦ Type@i ⟧ ρ ↘ 𝕌@i }} )
| eval_exp_var :
  `( {{ ⟦ # x ⟧ ρ ↘ ~(ρ x) }} )
| eval_exp_nat :
  `( {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} )
| eval_exp_zero :
  `( {{ ⟦ zero ⟧ ρ ↘ zero }} )
| eval_exp_succ :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ succ M ⟧ ρ ↘ succ m }} )
| eval_exp_natrec :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r }} )
| eval_exp_pi :
  `( {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ Π A B ⟧ ρ ↘ Π a ρ B }} )
| eval_exp_fn :
  `( {{ ⟦ λ A M ⟧ ρ ↘ λ ρ M }} )
| eval_exp_app :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ N ⟧ ρ ↘ n }} ->
     {{ $| m & n |↘ r }} ->
     {{ ⟦ M N ⟧ ρ ↘ r }} )
| eval_exp_sub :
  `( {{ ⟦ σ ⟧s ρ ↘ ρ' }} ->
     {{ ⟦ M ⟧ ρ' ↘ m }} ->
     {{ ⟦ M[σ] ⟧ ρ ↘ m }} )
where "'⟦' e '⟧' ρ '↘' r" := (eval_exp e ρ r) (in custom judg)
with eval_natrec : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ mz }} )
| eval_natrec_succ :
  `( {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ ⟦ MS ⟧ ρ ↦ b ↦ r ↘ ms }} ->
     {{ rec succ b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ms }} )
| eval_natrec_neut :
  `( {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ ⟦ A ⟧ ρ ↦ ⇑ ℕ m ↘ a }} ->
     {{ rec ⇑ ℕ m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ⇑ a (rec m under ρ return A | zero -> mz | succ -> MS end) }} )
where "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" := (eval_natrec A MZ MS m ρ r) (in custom judg)
with eval_app : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( {{ ⟦ M ⟧ ρ ↦ n ↘ m }} ->
     {{ $| λ ρ M & n |↘ m }} )
| eval_app_neut :
  `( {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
     {{ $| ⇑ (Π a ρ B) m & n |↘ ⇑ b (m (⇓ a n)) }} )
where "'$|' m '&' n '|↘' r" := (eval_app m n r) (in custom judg)
with eval_sub : sub -> env -> env -> Prop :=
| eval_sub_id :
  `( {{ ⟦ Id ⟧s ρ ↘ ρ }} )
| eval_sub_weaken :
  `( {{ ⟦ Wk ⟧s ρ ↘ ρ ↯ }} )
| eval_sub_extend :
  `( {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ σ ,, M ⟧s ρ ↘ ρσ ↦ m }} )
| eval_sub_compose :
  `( {{ ⟦ τ ⟧s ρ ↘ ρτ }} ->
     {{ ⟦ σ ⟧s ρτ ↘ ρτσ }} ->
     {{ ⟦ σ ∘ τ ⟧s ρ ↘ ρτσ }} )
where "'⟦' σ '⟧s' ρ '↘' ρσ" := (eval_sub σ ρ ρσ) (in custom judg)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_sub_mut_ind := Induction for eval_sub Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind,
  eval_sub_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_sub : mcltt.
