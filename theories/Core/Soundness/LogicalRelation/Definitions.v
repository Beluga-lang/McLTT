From Coq Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions Evaluation Readback PER.Definitions.
From Mcltt Require Export Domain.
From Mcltt.Core.Soundness Require Export Weakening.Definition.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'typ_pred'" := (predicate (Tcons ctx (Tcons typ Tnil))).
Notation "'typ_pred_equivalence'" := (@predicate_equivalence (Tcons ctx (Tcons typ Tnil))).
Notation "'glu_pred'" := (predicate (Tcons ctx (Tcons exp (Tcons typ (Tcons domain Tnil))))).
Notation "'glu_pred_equivalence'" := (@predicate_equivalence (Tcons ctx (Tcons exp (Tcons typ (Tcons domain Tnil))))).

Definition univ_typ_pred j i : typ_pred := fun Γ T => {{ Γ ⊢ T ≈ Type@j :  Type@i }}.
Arguments univ_typ_pred j i Γ T/.

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

#[export]
 Hint Constructors glu_nat : mcltt.

Definition nat_typ_pred i : typ_pred := fun Γ M => {{ Γ ⊢ M ≈ ℕ : Type@i }}.
Arguments nat_typ_pred i Γ M/.

Definition nat_glu_pred i : glu_pred := fun Γ m M a => nat_typ_pred i Γ M /\ glu_nat Γ m a.
Arguments nat_glu_pred i Γ m M a/.

Definition neut_typ_pred i C : typ_pred :=
  fun Γ M => {{ Γ ⊢ M : Type@i }} /\
            (forall Δ σ V, {{ Δ ⊢w σ : Γ }} -> {{ Rne C in length Δ ↘ V }} -> {{ Δ ⊢ M [ σ ] ≈ V : Type@i }}).
Arguments neut_typ_pred i C Γ M/.

Inductive neut_glu_pred i C : glu_pred :=
| ngp_make : forall Γ m M A c,
    neut_typ_pred i C Γ M ->
    per_bot c c ->
    (forall Δ σ V v, {{ Δ ⊢w σ : Γ }} ->
                {{ Rne C in length Δ ↘ V }} ->
                {{ Rne c in length Δ ↘ v }} ->
                {{ Δ ⊢ m [ σ ] ≈ v : M [ σ ] }}) ->
    neut_glu_pred i C Γ m M d{{{ ⇑ A c }}}.

Inductive pi_typ_pred i
  (IR : relation domain)
  (IP : typ_pred)
  (IEl : glu_pred)
  (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  typ_pred) : typ_pred :=
| ptp_make : forall Γ IT OT M,
    {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
    {{ Γ , IT ⊢ OT : Type@i }} ->
    (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> IP Δ {{{ IT [ σ ] }}}) ->
    (forall Δ σ m a, {{ Δ ⊢w σ : Γ }} -> IEl Δ m {{{ IT [ σ ] }}} a -> forall (Ha : IR a a), OP _ _ Ha Δ {{{ OT [ σ ,, m ] }}}) ->
    pi_typ_pred i IR IP IEl OP Γ M.

Inductive pi_glu_pred i
  (IR : relation domain)
  (IP : typ_pred)
  (IEl : glu_pred)
  (elem_rel : relation domain)
  (OEl : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  glu_pred): glu_pred :=
| pgp_make : forall Γ IT OT m M a,
    {{ Γ ⊢ m : M }} ->
    elem_rel a a ->
    {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
    {{ Γ , IT ⊢ OT : Type@i }} ->
    (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> IP Δ {{{ IT [ σ ] }}}) ->
    (forall Δ σ m' b, {{ Δ ⊢w σ : Γ }} -> IEl Δ m' {{{ IT [ σ ] }}} b -> forall (Ha : IR b b),
                   exists ab, {{ $| a & b |↘ ab }} /\ OEl _ _ Ha Δ {{{ m [ σ ] m' }}} {{{ OT [ σ ,, m' ] }}} ab) ->
    pi_glu_pred i IR IP IEl elem_rel OEl Γ m M a.


Lemma pi_glu_pred_pi_typ_pred : forall i IR IP IEl (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ IR }}),  typ_pred) elem_rel OEl Γ m M a,
    pi_glu_pred i IR IP IEl elem_rel OEl Γ m M a ->
    (forall Δ m' M' b c c' (Hc : IR c c'), OEl _ _ Hc Δ m' M' b -> OP _ _ Hc Δ M') ->
    pi_typ_pred i IR IP IEl OP Γ M.
Proof.
  inversion_clear 1; econstructor; eauto.
  intros.
  edestruct H5 as [? []]; eauto.
Qed.

Section Gluing.
  Variable
    (i : nat)
      (glu_univ_typ_rec : forall {j}, j < i -> domain -> typ_pred).

  Definition univ_glu_pred' {j} (lt_j_i : j < i) : glu_pred :=
    fun Γ m M A =>
      {{ Γ ⊢ m : M }} /\ {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
        per_univ j A A /\
        glu_univ_typ_rec lt_j_i A Γ m.

  #[global]
    Arguments univ_glu_pred' {j} lt_j_i Γ m M A/.

  Inductive glu_univ_elem_core : typ_pred -> glu_pred -> domain -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : j < i),
          j = j' ->
          typ_rel <∙> univ_typ_pred j i ->
          el_rel <∙> univ_glu_pred' lt_j_i ->
          glu_univ_elem_core typ_rel el_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}} }

  | glu_univ_elem_core_nat :
    `{ forall typ_rel el_rel,
          typ_rel <∙> nat_typ_pred i ->
          el_rel <∙> nat_glu_pred i ->
          glu_univ_elem_core typ_rel el_rel d{{{ ℕ }}} d{{{ ℕ }}} }

  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), typ_pred)
         (OEl : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), glu_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          glu_univ_elem_core IP IEl a a' ->
          per_univ_elem i in_rel a a' ->
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) b b',
              {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
              {{ ⟦ B' ⟧ p' ↦ c' ↘ b' }} ->
              glu_univ_elem_core (OP _ _ equiv_c_c') (OEl _ _ equiv_c_c') b b') ->
          per_univ_elem i elem_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}} ->
          typ_rel <∙> pi_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_pred i in_rel IP IEl elem_rel OEl ->
          glu_univ_elem_core typ_rel el_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}} }

  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          {{ Dom b ≈ b' ∈ per_bot }} ->
          typ_rel <∙> neut_typ_pred i b ->
          el_rel <∙> neut_glu_pred i b ->
          glu_univ_elem_core typ_rel el_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}} }.

End Gluing.

#[export]
Hint Constructors glu_univ_elem_core : mcltt.


Equations glu_univ_elem (i : nat) : typ_pred -> glu_pred -> domain -> domain -> Prop by wf i :=
| i => glu_univ_elem_core i (fun j lt_j_i A Γ M => exists P El, glu_univ_elem j P El A A /\ P Γ M).


Definition glu_univ (i : nat) (A : domain) : typ_pred :=
  fun Γ M => exists P El, glu_univ_elem i P El A A /\ P Γ M.

Definition univ_glu_pred j i : glu_pred :=
    fun Γ m M A =>
      {{ Γ ⊢ m : M }} /\ {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
        per_univ j A A /\
        glu_univ j A Γ m.

Section GluingInduction.

  Hypothesis
    (motive : nat -> typ_pred -> glu_pred -> domain -> domain -> Prop)

      (case_univ :
        forall i (j j' : nat)
          (typ_rel : typ_pred) (el_rel : glu_pred) (lt_j_i : j < i),
          j = j' ->
          (forall P El A B, glu_univ_elem j P El A B -> motive j P El A B) ->
          typ_rel <∙> univ_typ_pred j i ->
          el_rel <∙> univ_glu_pred j i ->
          motive i typ_rel el_rel d{{{ 𝕌 @ j }}} d{{{ 𝕌 @ j' }}})

      (case_nat :
        forall i (typ_rel : typ_pred) (el_rel : glu_pred),
          typ_rel <∙> nat_typ_pred i ->
          el_rel <∙> nat_glu_pred i ->
          motive i typ_rel el_rel d{{{ ℕ }}} d{{{ ℕ }}})

      (case_pi :
        forall i (a a' : domain) (B : typ) (p : env) (B' : typ) (p' : env) (in_rel : relation domain) (IP : typ_pred)
          (IEl : glu_pred) (OP : forall c c' : domain, {{ Dom c ≈ c' ∈ in_rel }} -> typ_pred)
          (OEl : forall c c' : domain, {{ Dom c ≈ c' ∈ in_rel }} -> glu_pred) (typ_rel : typ_pred) (el_rel : glu_pred)
          (elem_rel : relation domain),
          glu_univ_elem i IP IEl a a' ->
          motive i IP IEl a a' ->
          per_univ_elem i in_rel a a' ->
          (forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) (b b' : domain),
              {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
              {{ ⟦ B' ⟧ p' ↦ c' ↘ b' }} -> glu_univ_elem i (OP c c' equiv_c_c') (OEl c c' equiv_c_c') b b') ->
          (forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) (b b' : domain),
              {{ ⟦ B ⟧ p ↦ c ↘ b }} -> {{ ⟦ B' ⟧ p' ↦ c' ↘ b' }} -> motive i (OP c c' equiv_c_c') (OEl c c' equiv_c_c') b b') ->
          per_univ_elem i elem_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}} ->
          typ_rel <∙> pi_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_pred i in_rel IP IEl elem_rel OEl ->
          motive i typ_rel el_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}})

      (case_neut :
        forall i (b b' : domain_ne) (a a' : domain)
          (typ_rel : typ_pred)
          (el_rel : glu_pred),
          {{ Dom b ≈ b' ∈ per_bot }} ->
          typ_rel <∙> neut_typ_pred i b ->
          el_rel <∙> neut_glu_pred i b ->
          motive i typ_rel el_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}})
  .


  #[local]
    Ltac def_simp := simp glu_univ_elem in *.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
    Equations glu_univ_elem_ind i P El a b
    (H : glu_univ_elem i P El a b) : motive i P El a b by wf i :=
  | i, P, El, a, b, H =>
      glu_univ_elem_core_ind
        i
        (fun j lt_j_i A Γ M => glu_univ j A Γ M)
        (motive i)
        (fun j j' typ_rel el_rel lt_j_i Heq Htr Hel =>
           case_univ i j j' typ_rel el_rel lt_j_i
             Heq
             (fun P El A B H => glu_univ_elem_ind j P El A B H)
             Htr
             Hel)
        (case_nat i)
        _ (* (case_pi i) *)
        (case_neut i)
        P El a b
        _.
  Next Obligation.
    eapply (case_pi i); def_simp; eauto.
  Qed.

End GluingInduction.


Inductive glu_neut i Γ m M c A B : Prop :=
| glu_neut_make : forall P El,
    {{ Γ ⊢ m : M }} ->
    glu_univ_elem i P El A B ->
    per_bot c c ->
    (forall Δ σ a, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ a }} -> {{ Δ ⊢ m [ σ ] ≈  a : M [ σ ] }}) ->
    glu_neut i Γ m M c A B.


Inductive glu_normal i Γ m M a A B : Prop :=
| glu_normal_make : forall P El,
    {{ Γ ⊢ m : M }} ->
    glu_univ_elem i P El A B ->
    per_top d{{{ ⇓ A a }}} d{{{ ⇓ B a }}} ->
    (forall Δ σ b, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ A a in length Δ ↘ b }} -> {{ Δ ⊢ m [ σ ] ≈  b : M [ σ ] }}) ->
    glu_normal i Γ m M a A B.


Inductive glu_typ i Γ M A B : Prop :=
| glu_typ_make : forall P El,
    {{ Γ ⊢ M : Type@i }} ->
    glu_univ_elem i P El A B ->
    per_top_typ A B ->
    (forall Δ σ a, {{ Δ ⊢w σ : Γ }} -> {{ Rtyp A in length Δ ↘ a }} -> {{ Δ ⊢ M [ σ ] ≈  a : Type@i }}) ->
    glu_typ i Γ M A B.
