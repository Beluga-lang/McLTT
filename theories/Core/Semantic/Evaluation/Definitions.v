From Mcltt Require Import Base.
From Mcltt Require Export Domain.
Import Domain_Notations.

Reserved Notation "'⟦' M '⟧' p '↘' r" (in custom judg at level 80, M custom exp at level 99, p custom domain at level 99, r custom domain at level 99).
Reserved Notation "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' p '↘' r" (in custom judg at level 80, m custom domain at level 99, A custom exp at level 99, MZ custom exp at level 99, MS custom exp at level 99, p custom domain at level 99, r custom domain at level 99).
Reserved Notation "'$|' m '&' n '|↘' r" (in custom judg at level 80, m custom domain at level 99, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'⟦' σ '⟧s' p '↘' p'" (in custom judg at level 80, σ custom exp at level 99, p custom domain at level 99, p' custom domain at level 99).

Generalizable All Variables.

Inductive eval_exp : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( {{ ⟦ Type@i ⟧ p ↘ 𝕌@i }} )
| eval_exp_var :
  `( {{ ⟦ # x ⟧ p ↘ ~(p x) }} )
| eval_exp_nat :
  `( {{ ⟦ ℕ ⟧ p ↘ ℕ }} )
| eval_exp_zero :
  `( {{ ⟦ zero ⟧ p ↘ zero }} )
| eval_exp_succ :
  `( {{ ⟦ M ⟧ p ↘ m }} ->
     {{ ⟦ succ M ⟧ p ↘ succ m }} )
| eval_exp_natrec :
  `( {{ ⟦ M ⟧ p ↘ m }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
     {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ p ↘ r }} )
| eval_exp_pi :
  `( {{ ⟦ A ⟧ p ↘ a }} ->
     {{ ⟦ Π A B ⟧ p ↘ Π a p B }} )
| eval_exp_fn :
  `( {{ ⟦ λ A M ⟧ p ↘ λ p M }} )
| eval_exp_app :
  `( {{ ⟦ M ⟧ p ↘ m }} ->
     {{ ⟦ N ⟧ p ↘ n }} ->
     {{ $| m & n |↘ r }} ->
     {{ ⟦ M N ⟧ p ↘ r }} )
| eval_exp_sub :
  `( {{ ⟦ σ ⟧s p ↘ p' }} ->
     {{ ⟦ M ⟧ p' ↘ m }} ->
     {{ ⟦ M[σ] ⟧ p ↘ m }} )
where "'⟦' e '⟧' p '↘' r" := (eval_exp e p r) (in custom judg)
with eval_natrec : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( {{ ⟦ MZ ⟧ p ↘ mz }} ->
     {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ mz }} )
| eval_natrec_succ :
  `( {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
     {{ ⟦ MS ⟧ p ↦ b ↦ r ↘ ms }} ->
     {{ rec succ b ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ ms }} )
| eval_natrec_neut :
  `( {{ ⟦ MZ ⟧ p ↘ mz }} ->
     {{ ⟦ A ⟧ p ↦ ⇑ ℕ m ↘ a }} ->
     {{ rec ⇑ ℕ m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ ⇑ a (rec m under p return A | zero -> mz | succ -> MS end) }} )
where "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' p '↘' r" := (eval_natrec A MZ MS m p r) (in custom judg)
with eval_app : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( {{ ⟦ M ⟧ p ↦ n ↘ m }} ->
     {{ $| λ p M & n |↘ m }} )
| eval_app_neut :
  `( {{ ⟦ B ⟧ p ↦ n ↘ b }} ->
     {{ $| ⇑ (Π a p B) m & n |↘ ⇑ b (m (⇓ a n)) }} )
where "'$|' m '&' n '|↘' r" := (eval_app m n r) (in custom judg)
with eval_sub : sub -> env -> env -> Prop :=
| eval_sub_id :
  `( {{ ⟦ Id ⟧s p ↘ p }} )
| eval_sub_weaken :
  `( {{ ⟦ Wk ⟧s p ↘ p↯ }} )
| eval_sub_extend :
  `( {{ ⟦ σ ⟧s p ↘ p' }} ->
     {{ ⟦ M ⟧ p ↘ m }} ->
     {{ ⟦ σ ,, M ⟧s p ↘ p' ↦ m }} )
| eval_sub_compose :
  `( {{ ⟦ τ ⟧s p ↘ p' }} ->
     {{ ⟦ σ ⟧s p' ↘ p'' }} ->
     {{ ⟦ σ ∘ τ ⟧s p ↘ p'' }} )
where "'⟦' σ '⟧s' p '↘' p'" := (eval_sub σ p p') (in custom judg)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_sub_mut_ind := Induction for eval_sub Sort Prop.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_sub : mcltt.
