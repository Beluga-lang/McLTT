From Coq Require Import Relation_Definitions RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions Evaluation Readback PER.Definitions.
From Mcltt Require Export Domain.
From Mcltt.Core.Soundness Require Export Weakening.

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
     (forall {Δ σ v}, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ v }} -> {{ Δ ⊢ m [ σ ] ≈ v : ℕ }}) ->
     glu_nat Γ m d{{{ ⇑ ℕ c }}} ).

Definition nat_typ_pred Γ i : typ_pred := fun M => {{ Γ ⊢ M ≈ ℕ :  Type@i }}.

Definition nat_glu_pred Γ i : glu_pred := fun m M a => nat_typ_pred Γ i M /\ glu_nat Γ m a.

Definition neut_typ_pred Γ i C : typ_pred :=
  fun M => {{ Γ ⊢ M : Type@i }} /\
          (forall Δ σ V, {{ Δ ⊢w σ : Γ }} -> {{ Rne C in length Δ ↘ V }} -> {{ Δ ⊢ M [ σ ] ≈ V : Type@i }}).

Inductive neut_glu_pred Γ i C : glu_pred :=
| ngp_make : forall m M A c,
    neut_typ_pred Γ i C M ->
    per_bot c c ->
    (forall Δ σ V v, {{ Δ ⊢w σ : Γ }} ->
                {{ Rne C in length Δ ↘ V }} ->
                {{ Rne c in length Δ ↘ v }} ->
                {{ Δ ⊢ m [ σ ] ≈ v : M [ σ ] }}) ->
    neut_glu_pred Γ i C m M d{{{ ⇑ A c }}}.

Inductive pi_typ_pred Γ i
  (IR : relation domain)
  (IP : typ_pred)
  (IEl : glu_pred)
  (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  typ_pred) : typ_pred :=
| ptp_make : forall IT OT M,
    {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
    {{ Γ , IT ⊢ OT : Type@i }} ->
    (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> IP {{{ IT [ σ ] }}}) ->
    (forall Δ σ m a, {{ Δ ⊢w σ : Γ }} -> IEl m {{{ IT [ σ ] }}} a -> forall (Ha : IR a a), OP _ _ Ha {{{ OT [ σ ,, m ] }}}) ->
    pi_typ_pred Γ i IR IP IEl OP M.

Inductive pi_glu_pred Γ i
  (IR : relation domain)
  (IP : typ_pred)
  (IEl : glu_pred)
  (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  typ_pred)
  (elem_rel : relation domain)
  (OEl : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  glu_pred): glu_pred :=
| pgp_make : forall IT OT m M a,
    {{ Γ ⊢ m : M }} ->
    elem_rel a a ->
    {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
    {{ Γ , IT ⊢ OT : Type@i }} ->
    (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> IP {{{ IT [ σ ] }}}) ->
    (forall Δ σ m' b, {{ Δ ⊢w σ : Γ }} -> IEl m' {{{ IT [ σ ] }}} b -> forall (Ha : IR b b),
    exists ab, {{ $| a & b |↘ ab }} /\ OEl _ _ Ha {{{ m [ σ ] m' }}} {{{ OT [ σ ,, m' ] }}} ab) ->
    pi_glu_pred Γ i IR IP IEl OP elem_rel OEl m M a.


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

  Inductive glu_univ_elem_core : ctx -> typ_pred -> glu_pred -> relation domain -> domain -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
         typ_rel
         el_rel
         (lt_j_i : j < i),
          j = j' ->
          (elem_rel <~> glu_univ_rec lt_j_i) ->
          typ_rel <∙> univ_typ_pred Γ j i ->
          el_rel <∙> univ_glu_pred Γ lt_j_i ->
          glu_univ_elem_core Γ typ_rel el_rel elem_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}} }

  | glu_univ_elem_core_nat :
    `{ forall (elem_rel : relation domain)
         typ_rel el_rel,
          (elem_rel <~> per_nat) ->
          typ_rel <∙> nat_typ_pred Γ i ->
          el_rel <∙> nat_glu_pred Γ i ->
          glu_univ_elem_core Γ nat_rel el_rel elem_rel d{{{ ℕ }}} d{{{ ℕ }}} }

  (* | glu_univ_elem_core_pi : *)
  (*   `{ forall (in_rel : relation domain) *)
  (*        IP IEl *)
  (*        (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain) *)
  (*        typ_rel el_rel *)
  (*        (elem_rel : relation domain), *)
  (*         glu_univ_elem_core Γ in_rel IP IEl a a' -> *)
  (*         (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), *)
  (*             rel_mod_eval per_univ_elem_core B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) -> *)

  (*         (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) -> *)
  (*         glu_univ_elem_core Γ typ_rel el_rel elem_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}} } *)

  | glu_univ_elem_core_neut :
    `{ forall (elem_rel : relation domain)
         typ_rel el_rel,
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          typ_rel <∙> neut_typ_pred Γ i b ->
          el_rel <∙> neut_glu_pred Γ i b ->
          glu_univ_elem_core Γ typ_rel el_rel elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}} }.

End Gluing.
