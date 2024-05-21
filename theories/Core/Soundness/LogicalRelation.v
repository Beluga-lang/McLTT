From Coq Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions Evaluation Readback PER.Definitions.
From Mcltt Require Export Domain.
From Mcltt.Core.Soundness Require Export Weakening.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'typ_pred'" := (predicate (Tcons ctx (Tcons typ Tnil))).
Notation "'glu_pred'" := (predicate (Tcons ctx (Tcons exp (Tcons typ (Tcons domain Tnil))))).

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
      (glu_univ_rec : forall {j}, j < i -> relation domain)
      (glu_univ_typ_rec : forall {j}, j < i -> typ_pred).

  Definition univ_glu_pred {j} (lt_j_i : j < i) : glu_pred :=
    fun Γ m M A =>
      {{ Γ ⊢ m : M }} /\ {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
        glu_univ_rec lt_j_i A A /\
        glu_univ_typ_rec lt_j_i Γ m.

  #[global]
    Arguments univ_glu_pred {j} lt_j_i Γ m M A/.

  Inductive glu_univ_elem_core : typ_pred -> glu_pred -> relation domain -> domain -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
         typ_rel
         el_rel
         (lt_j_i : j < i),
          j = j' ->
          (elem_rel <~> glu_univ_rec lt_j_i) ->
          typ_rel <∙> univ_typ_pred j i ->
          el_rel <∙> univ_glu_pred lt_j_i ->
          glu_univ_elem_core typ_rel el_rel elem_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}} }

  | glu_univ_elem_core_nat :
    `{ forall (elem_rel : relation domain)
         typ_rel el_rel,
          (elem_rel <~> per_nat) ->
          typ_rel <∙> nat_typ_pred i ->
          el_rel <∙> nat_glu_pred i ->
          glu_univ_elem_core typ_rel el_rel elem_rel d{{{ ℕ }}} d{{{ ℕ }}} }

  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
         (OP : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), typ_pred)
         (OEl : forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), glu_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          glu_univ_elem_core IP IEl in_rel a a' ->
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval (glu_univ_elem_core (OP _ _ equiv_c_c') (OEl _ _ equiv_c_c'))
                B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}}
                (out_rel equiv_c_c')) ->
          (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
          typ_rel <∙> pi_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_pred i in_rel IP IEl elem_rel OEl ->
          glu_univ_elem_core typ_rel el_rel elem_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}} }

  | glu_univ_elem_core_neut :
    `{ forall (elem_rel : relation domain)
         typ_rel el_rel,
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          typ_rel <∙> neut_typ_pred i b ->
          el_rel <∙> neut_glu_pred i b ->
          glu_univ_elem_core typ_rel el_rel elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}} }.


  Hypothesis
    (motive : typ_pred -> glu_pred -> relation domain -> domain -> domain -> Prop)

      (case_univ :
        forall {j j' : nat} (elem_rel : relation domain)
          (typ_rel : typ_pred) (el_rel : glu_pred) (lt_j_i : j < i),
          j = j' ->
          elem_rel <~> glu_univ_rec lt_j_i ->
          typ_rel <∙> univ_typ_pred j i ->
          el_rel <∙> univ_glu_pred lt_j_i ->
          motive typ_rel el_rel elem_rel d{{{ 𝕌 @ j }}} d{{{ 𝕌 @ j' }}})

      (case_nat :
        forall (elem_rel : relation domain)
          (typ_rel : typ_pred) (el_rel : glu_pred),
          elem_rel <~> per_nat ->
          typ_rel <∙> nat_typ_pred i ->
          el_rel <∙> nat_glu_pred i ->
          motive typ_rel el_rel elem_rel d{{{ ℕ }}} d{{{ ℕ }}})

      (case_pi :
        forall {a a' : domain} {B : typ} {p : env} {B' : typ}
          {p' : env} (in_rel : relation domain) (IP : typ_pred)
          (IEl : glu_pred)
          (out_rel : forall c c' : domain,
              {{ Dom c ≈ c' ∈ in_rel }} -> relation domain)
          (OP : forall c c' : domain, {{ Dom c ≈ c' ∈ in_rel }} -> typ_pred)
          (OEl : forall c c' : domain,
              {{ Dom c ≈ c' ∈ in_rel }} -> glu_pred)
          (typ_rel : typ_pred) (el_rel : glu_pred)
          (elem_rel : relation domain),
          glu_univ_elem_core IP IEl in_rel a a' ->
          motive IP IEl in_rel a a' ->
          (forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval
                (fun R A B => glu_univ_elem_core (OP c c' equiv_c_c') (OEl c c' equiv_c_c') R A B /\ motive (OP c c' equiv_c_c') (OEl c c' equiv_c_c') R A B)
                B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel c c' equiv_c_c')) ->
          elem_rel <~>
            (fun f f' : domain =>
               forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
                 rel_mod_app f c f' c' (out_rel c c' equiv_c_c')) ->
          typ_rel <∙> pi_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_pred i in_rel IP IEl elem_rel OEl ->
          motive typ_rel el_rel elem_rel d{{{ Π a p B }}} d{{{ Π a' p' B' }}})

      (case_neut :
        forall {b b' : domain_ne} {a a' : domain}
          (elem_rel : relation domain) (typ_rel : typ_pred)
          (el_rel : glu_pred),
          {{ Dom b ≈ b' ∈ per_bot }} ->
          elem_rel <~> per_ne ->
          typ_rel <∙> neut_typ_pred i b ->
          el_rel <∙> neut_glu_pred i b ->
          motive typ_rel el_rel elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}})
  .


  #[derive(equations=no, eliminator=no)]
    Equations glu_univ_elem_core_strong_ind P El R a b
    (H : glu_univ_elem_core P El R a b) : motive P El R a b :=
  | P, El, R, a, b, (glu_univ_elem_core_univ R P El lt_j_i Heq HR HP HEl) =>
      case_univ R P El lt_j_i Heq HR HP HEl
  | P, El, R, a, b, (glu_univ_elem_core_nat R P El HR HP HEl) =>
      case_nat R P El HR HP HEl
  | P, El, R, a, b, (glu_univ_elem_core_pi in_rel IP IEl out_rel OP OEl P El R H HT HR HP HEl) =>
      case_pi in_rel IP IEl out_rel OP OEl P El R
        H (glu_univ_elem_core_strong_ind _ _ _ _ _ H)
        (fun c c' Hc => match HT _ _ Hc with
                     | mk_rel_mod_eval b b' evb evb' Rel =>
                         mk_rel_mod_eval b b' evb evb' (conj _ (glu_univ_elem_core_strong_ind _ _ _ _ _ Rel))
                     end)
        HR HP HEl
  | P, El, R, a, b, (glu_univ_elem_core_neut R P El H HR HP HEl) =>
      case_neut R P El H HR HP HEl.

End Gluing.
