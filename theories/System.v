Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.

Reserved Notation "⊢ Γ" (at level 80).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).
Reserved Notation "Γ ⊢ [ e ] : T" (no associativity, at level 80, e at next level).

Inductive wf_ctx : Ctx -> Set :=
  | wf_empty : ⊢ []
  | wf_ext : ∀ Γ t, ⊢ Γ -> ⊢ t :: Γ
where "⊢ Γ" := (wf_ctx Γ)
with wf_term : Ctx -> exp -> Typ -> Set :=
  | wf_univ_nat_f :
      ∀ Γ i,
      ⊢ Γ -> Γ ⊢ ℕ : typ i
  | wf_univ :
      ∀ Γ i,
      ⊢ Γ -> Γ ⊢ typ i : typ (i + 1)
  | wf_univ_fun_f :
      ∀ Γ a b i,
      Γ ⊢ a : typ i ->
      a :: Γ ⊢ b : typ i ->
      Γ ⊢ 𝝺 a b : typ i
  | wf_pi :
      ∀ Γ i (S T : Typ),
      Γ ⊢ S : typ i ->
      S :: Γ ⊢ T : typ (i + 1) ->
      Γ ⊢ Π S T : typ (i + 1)
  | wf_hyp :
      ∀ Γ t i,
      ⊢ t :: Γ ->
      t :: Γ ⊢ a_var i : (a_sub t a_weaken)
  | wf_fun_e:
      ∀ Γ M N A B i,
      Γ ⊢ M : Π A B ->
      Γ ⊢ N : A ->
      A :: Γ ⊢ B : typ i ->
      Γ ⊢ a_app M N : a_sub B (a_extend a_id N)
  | wf_fun_i :
      ∀ Γ M A B i,
      Γ ⊢ A : typ i ->
      A :: Γ ⊢ M : B ->
      Γ ⊢ 𝝺 A M : Π A B
  | wf_zero :
      ∀ Γ, ⊢ Γ -> Γ ⊢ a_zero : ℕ
  | wf_succ :
      ∀ Γ n, Γ ⊢ n : ℕ -> Γ ⊢ a_succ n : ℕ
where "Γ ⊢ t : T" := (wf_term Γ t T)
with wf_sb : Ctx -> Sb -> Ctx -> Set :=
  | wf_sb_id : ∀ Γ,
      ⊢ Γ -> Γ ⊢ [a_id] : Γ
  | wf_sb_weaken : ∀ Γ A i,
      Γ ⊢ A : typ i ->
      A :: Γ ⊢ [a_weaken] : Γ
  | wf_sb_compose : ∀ Γ1 Γ2 Γ3 s1 s2,
      Γ1 ⊢ [s2] : Γ2 ->
      Γ2 ⊢ [s1] : Γ3 ->
      Γ1 ⊢ [a_compose s1 s2] : Γ3
  | wf_sb_extend : ∀ Γ S Δ M A i,
      Γ ⊢ [S] : Δ ->
      Δ ⊢ A : typ i ->
      Γ ⊢ M : a_sub A S ->
      Γ ⊢ [a_extend S M] : A :: Δ
where "Γ ⊢ [ e ] : T" := (wf_sb Γ e T).
