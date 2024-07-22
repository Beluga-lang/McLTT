From Coq Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import System.Definitions.
From Mcltt.Core Require Export Domain PER.Definitions Soundness.Weakening.Definition.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'glu_typ_pred_args'" := (Tcons ctx (Tcons typ Tnil)).
Notation "'glu_typ_pred'" := (predicate glu_typ_pred_args).
Notation "'glu_typ_pred_equivalence'" := (@predicate_equivalence glu_typ_pred_args) (only parsing).
(* This type annotation is to distinguish this notation from others *)
Notation "Γ ⊢ A ® R" := ((R Γ A : Prop) : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, A custom exp, R constr).

Notation "'glu_exp_pred_args'" := (Tcons ctx (Tcons exp (Tcons typ (Tcons domain Tnil)))).
Notation "'glu_exp_pred'" := (predicate glu_exp_pred_args).
Notation "'glu_exp_pred_equivalence'" := (@predicate_equivalence glu_exp_pred_args) (only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ M A m : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp, m custom domain, R constr).

Notation "'glu_sub_pred_args'" := (Tcons ctx (Tcons sub (Tcons env Tnil))).
Notation "'glu_sub_pred'" := (predicate glu_sub_pred_args).
Notation "'glu_sub_pred_equivalence'" := (@predicate_equivalence glu_sub_pred_args) (only parsing).
Notation "Γ ⊢s σ ® ρ ∈ R" := (R Γ σ ρ : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, σ custom exp, ρ custom domain, R constr).

Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : (Prop : (Type : Type))) (in custom judg at level 90, a custom domain, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : (Prop : (Type : Type))) (in custom judg at level 90, A custom exp, R constr, Sb constr).

Inductive glu_nat : ctx -> exp -> domain -> Prop :=
| glu_nat_zero :
  `{ {{ Γ ⊢ m ≈ zero : ℕ }} ->
     glu_nat Γ m d{{{ zero }}} }
| glu_nat_succ :
  `{ {{ Γ ⊢ m ≈ succ m' : ℕ }} ->
     glu_nat Γ m' a ->
     glu_nat Γ m d{{{ succ a }}} }
| glu_nat_neut :
  `{ per_bot c c ->
     (forall {Δ σ v}, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ v }} -> {{ Δ ⊢ m[σ] ≈ v : ℕ }}) ->
     glu_nat Γ m d{{{ ⇑ ℕ c }}} }.

#[export]
Hint Constructors glu_nat : mcltt.

Definition nat_glu_typ_pred i : glu_typ_pred := fun Γ M => {{ Γ ⊢ M ≈ ℕ : Type@i }}.
Arguments nat_glu_typ_pred i Γ M/.

Definition nat_glu_exp_pred i : glu_exp_pred := fun Γ m M a => {{ Γ ⊢ M ® nat_glu_typ_pred i }} /\ glu_nat Γ m a.
Arguments nat_glu_exp_pred i Γ m M a/.

Definition neut_glu_typ_pred i C : glu_typ_pred :=
  fun Γ M => {{ Γ ⊢ M : Type@i }} /\
            (forall Δ σ V, {{ Δ ⊢w σ : Γ }} -> {{ Rne C in length Δ ↘ V }} -> {{ Δ ⊢ M[σ] ≈ V : Type@i }}).
Arguments neut_glu_typ_pred i C Γ M/.

Inductive neut_glu_exp_pred i C : glu_exp_pred :=
| mk_neut_glu_exp_pred :
    `{ {{ Γ ⊢ M ® neut_glu_typ_pred i C }} ->
       {{ Dom c ≈ c ∈ per_bot }} ->
       (forall Δ σ V v, {{ Δ ⊢w σ : Γ }} ->
                      {{ Rne C in length Δ ↘ V }} ->
                      {{ Rne c in length Δ ↘ v }} ->
                      {{ Δ ⊢ m[σ] ≈ v : M[σ] }}) ->
       {{ Γ ⊢ m : M ® ⇑ A c ∈ neut_glu_exp_pred i C }} }.

Inductive pi_glu_typ_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (OP : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_typ_pred) : glu_typ_pred :=
| mk_pi_glu_typ_pred :
    `{ {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
       {{ Γ , IT ⊢ OT : Type@i }} ->
       (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Δ ⊢ IT[σ] ® IP }}) ->
       (forall Δ σ m a,
           {{ Δ ⊢w σ : Γ }} ->
           {{ Δ ⊢ m : IT[σ] ® a ∈ IEl }} ->
           forall (equiv_a : {{ Dom a ≈ a ∈ IR }}),
             {{ Δ ⊢ OT[σ,,m] ® OP _ equiv_a }}) ->
       {{ Γ ⊢ M ® pi_glu_typ_pred i IR IP IEl OP }} }.

Inductive pi_glu_exp_pred i
  (IR : relation domain)
  (IP : glu_typ_pred)
  (IEl : glu_exp_pred)
  (elem_rel : relation domain)
  (OEl : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_exp_pred): glu_exp_pred :=
| mk_pi_glu_exp_pred :
  `{ {{ Γ ⊢ m : M }} ->
     {{ Dom a ≈ a ∈ elem_rel }} ->
     {{ Γ ⊢ M ≈ Π IT OT : Type@i }} ->
     {{ Γ , IT ⊢ OT : Type@i }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Δ ⊢ IT[σ] ® IP }}) ->
     (forall Δ σ m' b,
         {{ Δ ⊢w σ : Γ }} ->
         {{ Δ ⊢ m' : IT[ σ ] ® b ∈ IEl }} ->
         forall (equiv_b : {{ Dom b ≈ b ∈ IR }}),
         exists ab, {{ $| a & b |↘ ab }} /\ {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® ab ∈ OEl _ equiv_b }}) ->
     {{ Γ ⊢ m : M ® a ∈ pi_glu_exp_pred i IR IP IEl elem_rel OEl }} }.

#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mcltt.

Definition univ_glu_typ_pred j i : glu_typ_pred := fun Γ T => {{ Γ ⊢ T ≈ Type@j :  Type@i }}.
Arguments univ_glu_typ_pred j i Γ T/.

Section Gluing.
  Variable
    (i : nat)
      (glu_univ_typ_rec : forall {j}, j < i -> domain -> glu_typ_pred).

  Definition univ_glu_exp_pred' {j} (lt_j_i : j < i) : glu_exp_pred :=
    fun Γ m M A =>
      {{ Γ ⊢ m : M }} /\
        {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
        {{ Γ ⊢ m ® glu_univ_typ_rec lt_j_i A }}.

  #[global]
  Arguments univ_glu_exp_pred' {j} lt_j_i Γ m M A/.

  Inductive glu_univ_elem_core : glu_typ_pred -> glu_exp_pred -> domain -> Prop :=
  | glu_univ_elem_core_univ :
    `{ forall typ_rel
         el_rel
         (lt_j_i : j < i),
          typ_rel <∙> univ_glu_typ_pred j i ->
          el_rel <∙> univ_glu_exp_pred' lt_j_i ->
          {{ DG 𝕌@j ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_nat :
    `{ forall typ_rel el_rel,
          typ_rel <∙> nat_glu_typ_pred i ->
          el_rel <∙> nat_glu_exp_pred i ->
          {{ DG ℕ ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         IP IEl
         (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
         (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred)
         typ_rel el_rel
         (elem_rel : relation domain),
          {{ DG a ∈ glu_univ_elem_core ↘ IP ↘ IEl }} ->
          {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
          (forall {c} (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
              {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
              {{ DG b ∈ glu_univ_elem_core ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) ->
          {{ DF Π a p B ≈ Π a p B ∈ per_univ_elem i ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          {{ DG Π a p B ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_univ_elem_core_neut :
    `{ forall typ_rel el_rel,
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred i b ->
          el_rel <∙> neut_glu_exp_pred i b ->
          {{ DG ⇑ a b ∈ glu_univ_elem_core ↘ typ_rel ↘ el_rel }} }.
End Gluing.

#[export]
Hint Constructors glu_univ_elem_core : mcltt.

Equations glu_univ_elem (i : nat) : glu_typ_pred -> glu_exp_pred -> domain -> Prop by wf i :=
| i => glu_univ_elem_core i (fun j lt_j_i A Γ M => exists P El, {{ DG A ∈ glu_univ_elem j ↘ P ↘ El }} /\ {{ Γ ⊢ M ® P }}).

Definition glu_univ_typ (i : nat) (A : domain) : glu_typ_pred :=
  fun Γ M => exists P El, {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} /\ {{ Γ ⊢ M ® P }}.
Arguments glu_univ_typ i A Γ M/.

Definition univ_glu_exp_pred j i : glu_exp_pred :=
    fun Γ m M A =>
      {{ Γ ⊢ m : M }} /\ {{ Γ ⊢ M ≈ Type@j : Type@i }} /\
        {{ Γ ⊢ m ® glu_univ_typ j A }}.
Arguments univ_glu_exp_pred j i Γ t T a/.

Section GluingInduction.
  Hypothesis
    (motive : nat -> glu_typ_pred -> glu_exp_pred -> domain -> Prop)

      (case_univ :
        forall i (j : nat)
          (typ_rel : glu_typ_pred) (el_rel : glu_exp_pred) (lt_j_i : j < i),
          (forall P El A, {{ DG A ∈ glu_univ_elem j ↘ P ↘ El }} -> motive j P El A) ->
          typ_rel <∙> univ_glu_typ_pred j i ->
          el_rel <∙> univ_glu_exp_pred j i ->
          motive i typ_rel el_rel d{{{ 𝕌 @ j }}})

      (case_nat :
        forall i (typ_rel : glu_typ_pred) (el_rel : glu_exp_pred),
          typ_rel <∙> nat_glu_typ_pred i ->
          el_rel <∙> nat_glu_exp_pred i ->
          motive i typ_rel el_rel d{{{ ℕ }}})

      (case_pi :
        forall i (a : domain) (B : typ) (p : env) (in_rel : relation domain) (IP : glu_typ_pred)
          (IEl : glu_exp_pred) (OP : forall c : domain, {{ Dom c ≈ c ∈ in_rel }} -> glu_typ_pred)
          (OEl : forall c : domain, {{ Dom c ≈ c ∈ in_rel }} -> glu_exp_pred) (typ_rel : glu_typ_pred) (el_rel : glu_exp_pred)
          (elem_rel : relation domain),
          {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} ->
          motive i IP IEl a ->
          {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
          (forall (c : domain) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : domain),
              {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
              {{ DG b ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }}) ->
          (forall (c : domain) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : domain),
              {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
              motive i (OP c equiv_c) (OEl c equiv_c) b) ->
          {{ DF Π a p B ≈ Π a p B ∈ per_univ_elem i ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred i in_rel IP IEl OP ->
          el_rel <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl ->
          motive i typ_rel el_rel d{{{ Π a p B }}})

      (case_neut :
        forall i (b : domain_ne) (a : domain)
          (typ_rel : glu_typ_pred)
          (el_rel : glu_exp_pred),
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred i b ->
          el_rel <∙> neut_glu_exp_pred i b ->
          motive i typ_rel el_rel d{{{ ⇑ a b }}})
  .

  #[local]
  Ltac def_simp := simp glu_univ_elem in *.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations glu_univ_elem_ind i P El a
    (H : glu_univ_elem i P El a) : motive i P El a by wf i :=
  | i, P, El, a, H =>
      glu_univ_elem_core_ind
        i
        (fun j lt_j_i A Γ M => glu_univ_typ j A Γ M)
        (motive i)
        (fun j typ_rel el_rel lt_j_i Hty Hel =>
           case_univ i j typ_rel el_rel lt_j_i
             (fun P El A H => glu_univ_elem_ind j P El A H)
             Hty
             Hel)
        (case_nat i)
        _ (* (case_pi i) *)
        (case_neut i)
        P El a
        _.
  Next Obligation.
    eapply (case_pi i); def_simp; eauto.
  Qed.
End GluingInduction.

Inductive glu_neut i A Γ m M c : Prop :=
| mk_glu_neut :
    {{ Γ ⊢ m : M }} ->
    {{ Γ ⊢ M ® glu_univ_typ i A }} ->
    {{ Dom c ≈ c ∈ per_bot }} ->
    (forall Δ σ a, {{ Δ ⊢w σ : Γ }} -> {{ Rne c in length Δ ↘ a }} -> {{ Δ ⊢ m[σ] ≈ a : M[σ] }}) ->
    {{ Γ ⊢ m : M ® c ∈ glu_neut i A }}.

Inductive glu_norm i A Γ m M a : Prop :=
| mk_glu_norm :
    {{ Γ ⊢ m : M }} ->
    {{ Γ ⊢ M ® glu_univ_typ i A }} ->
    {{ Dom ⇓ A a ≈ ⇓ A a ∈ per_top }} ->
    (forall Δ σ b, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ A a in length Δ ↘ b }} -> {{ Δ ⊢ m [ σ ] ≈  b : M [ σ ] }}) ->
    {{ Γ ⊢ m : M ® a ∈ glu_norm i A }}.

Inductive glu_typ i A Γ M : Prop :=
| mk_glu_typ : forall P El,
    {{ Γ ⊢ M : Type@i }} ->
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    (forall Δ σ a, {{ Δ ⊢w σ : Γ }} -> {{ Rtyp A in length Δ ↘ a }} -> {{ Δ ⊢ M[σ] ≈ a : Type@i }}) ->
    {{ Γ ⊢ M ® glu_typ i A }}.

Ltac invert_glu_rel1 :=
  match goal with
  | H : pi_glu_typ_pred _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : pi_glu_exp_pred _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_typ_pred _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_exp_pred _ _ _ _ _ _ |- _ =>
      progressive_invert H
  end.

Variant glu_rel_typ_sub i Δ A σ ρ : Prop :=
| mk_glu_typ_sub :
  `{ forall P El,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        {{ Δ ⊢ A[σ] ® P }} ->
        glu_rel_typ_sub i Δ A σ ρ }.

Definition nil_glu_sub_pred : glu_sub_pred :=
  fun Δ σ ρ => {{ Δ ⊢s σ : ⋅ }}.
Arguments nil_glu_sub_pred Δ σ ρ/.

(* The parameters are ordered differently from the Agda version
   so that we can return "glu_sub_pred". *)
Variant cons_glu_sub_pred i Γ A (TSb : glu_sub_pred) : glu_sub_pred :=
| mk_cons_glu_sub_pred :
  `{ forall P El,
        {{ Δ ⊢s σ : Γ, A }} ->
        (* Do we need the following argument?
           In other words, is it possible to prove that "TSb" respects
           wf_sub_eq without the following condition? *)
        {{ Δ ⊢s Wk ∘ σ ≈ Wk∘σ : Γ }} ->
        {{ ⟦ A ⟧ ρ ↯ ↘ a }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        {{ Δ ⊢ #0[σ] : A[Wk∘σ] ® ~(ρ 0) ∈ El }} ->
        {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred i Γ A TSb }} }.

Inductive glu_ctx_env : glu_sub_pred -> ctx -> Prop :=
| glu_ctx_env_nil :
  `{ forall Sb,
        Sb <∙> nil_glu_sub_pred ->
        {{ EG ⋅ ∈ glu_ctx_env ↘ Sb }} }
| glu_ctx_env_cons :
  `{ forall i TSb Sb,
        {{ EG Γ ∈ glu_ctx_env ↘ TSb }} ->
        {{ Γ ⊢ A : Type@i }} ->
        (forall Δ σ ρ,
            {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
            glu_rel_typ_sub i Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred i Γ A TSb ->
        {{ EG Γ, A ∈ glu_ctx_env ↘ Sb }} }.

Variant glu_rel_exp_sub i Δ M A σ ρ : Prop :=
| mk_glu_exp_sub :
  `{ forall P El,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ ⟦ M ⟧ ρ ↘ m }} ->
        {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
        {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }} ->
        glu_rel_exp_sub i Δ M A σ ρ }.

Variant glu_rel_sub_sub Δ τ (Sb : glu_sub_pred) σ ρ : Prop :=
| mk_glu_sub_sub :
  `{ {{ ⟦ τ ⟧s ρ ↘ ρ' }} ->
     {{ Δ ⊢s τ ∘ σ ® ρ' ∈ Sb }} ->
     glu_rel_sub_sub Δ τ Sb σ ρ}.

Definition glu_rel_ctx Γ : Prop := exists Sb, {{ EG Γ ∈ glu_ctx_env ↘ Sb }}.
Arguments glu_rel_ctx Γ/.

Definition glu_rel_exp Γ M A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} /\
      exists i,
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_sub i Δ M A σ ρ.
Arguments glu_rel_exp Γ M A/.

Definition glu_rel_sub Γ τ Γ' : Prop :=
  exists Sb Sb',
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} /\
    {{ EG Γ' ∈ glu_ctx_env ↘ Sb' }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_sub_sub Δ τ Sb' σ ρ.
Arguments glu_rel_sub Γ τ Γ'/.

Notation "⊩ Γ" := (glu_rel_ctx Γ) (in custom judg at level 80, Γ custom exp).
Notation "Γ ⊩ M : A" := (glu_rel_exp Γ M A) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Notation "Γ ⊩s τ : Γ'" := (glu_rel_sub Γ τ Γ') (in custom judg at level 80, Γ custom exp, τ custom exp, Γ' custom exp).
