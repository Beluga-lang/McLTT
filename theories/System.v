Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.

Reserved Notation "⊢ Γ" (at level 80).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).

Inductive wf_ctx : Ctx -> Set :=
  | wf_empty : ⊢ []
  | wf_ext : ∀ Γ a, ⊢ Γ -> ⊢ a :: Γ
where "⊢ Γ" := (wf_ctx Γ)
with wf_term : Ctx -> exp -> Typ -> Set :=
  | wf_univ_unit :
      ∀ Γ i, ⊢ Γ -> Γ ⊢ n : typ i
  | wf_univ :
      ∀ Γ i, ⊢ Γ -> Γ ⊢ typ i : typ (i + 1)
  | wf_pi :
      ∀ Γ i (S T : Typ),
      Γ ⊢ S : typ i ->
      S :: Γ ⊢ T : typ (i + 1) ->
      Γ ⊢ (pi S T) : typ (i + 1)
where "Γ ⊢ t : T" := (wf_term Γ t T).
