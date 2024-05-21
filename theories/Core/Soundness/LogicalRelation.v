From Coq Require Import Relation_Definitions RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions Evaluation Readback PER.Definitions.
From Mcltt Require Export Domain.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'typ_pred'" := (predicate (Tcons typ Tnil)).
Notation "'glu_pred'" := (predicate (Tcons exp (Tcons typ (Tcons domain Tnil)))).

Definition univ_typ_pred Γ j i : typ_pred := fun T => {{ Γ ⊢ T ≈ Type@j :  Type@i }}.

Inductive glu_nat : ctx -> exp -> domain -> Prop :=
| glu_nat_zero :
  `( {{ Γ ⊢ m ≈ zero : ℕ }} ->
     glu_nat Γ m d{{{ zero }}} )
| glu_nat_succ :
  `( {{ Γ ⊢ m ≈ succ m' : ℕ }} ->
     glu_nat Γ m' a ->
     glu_nat Γ m d{{{ succ a }}} )
| glu_nat_neut :
  `( per_bot c c ->
     (* need to define weakenings *)
     glu_nat Γ m d{{{ ⇑ ℕ c }}} ).

Section Gluing.
  Variable
    (i : nat)
      (glu_univ_rec : forall {j}, j < i -> relation domain)
      (glu_univ_typ_rec : forall {j}, j < i -> typ_pred).

  Definition univ_glu_pred Γ {j} (lt_j_i : j < i) : glu_pred :=
    fun m M A =>
    {{ Γ ⊢ m : M }} /\ {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
      glu_univ_rec lt_j_i A A /\
      glu_univ_typ_rec lt_j_i m.

  Inductive glu_univ_elem_core : ctx -> relation domain -> typ_pred -> glu_pred -> domain -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
         typ_rel
         el_rel
         (lt_j_i : j < i),
          j = j' ->
          (elem_rel <~> glu_univ_rec lt_j_i) ->
          typ_rel <∙> univ_typ_pred Γ j i ->
          el_rel <∙> univ_glu_pred Γ lt_j_i ->
          glu_univ_elem_core Γ elem_rel typ_rel el_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}} }.

  (* | per_univ_elem_core_nat : *)
  (*   forall (elem_rel : relation domain), *)
  (*     (elem_rel <~> per_nat) -> *)
  (*     {{ DF ℕ ≈ ℕ ∈ per_univ_elem_core ↘ elem_rel }} *)
  (* | per_univ_elem_core_pi : *)
  (*   `{ forall (in_rel : relation domain) *)
  (*        (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain) *)
  (*        (elem_rel : relation domain) *)
  (*        (equiv_a_a' : {{ DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel}}), *)
  (*         PER in_rel -> *)
  (*         (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), *)
  (*             rel_mod_eval per_univ_elem_core B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) -> *)
  (*         (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) -> *)
  (*         {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem_core ↘ elem_rel }} } *)
  (* | per_univ_elem_core_neut : *)
  (*   `{ forall (elem_rel : relation domain), *)
  (*         {{ Dom b ≈ b' ∈ per_bot }} -> *)
  (*         (elem_rel <~> per_ne) -> *)
  (*         {{ DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ elem_rel }} } *)
  (* . *)

End Gluing.
