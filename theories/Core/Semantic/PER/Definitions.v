From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.
From Mcltt Require Import Base Evaluation LibTactics Readback.
From Mcltt Require Export Domain.
Import Domain_Notations.

Notation "'Dom' a ≈ b ∈ R" := ((R a b : Prop) : Prop) (in custom judg at level 90, a custom domain, b custom domain, R constr).
Notation "'DF' a ≈ b ∈ R ↘ R'" := ((R R' a b : Prop) : Prop) (in custom judg at level 90, a custom domain, b custom domain, R constr, R' constr).
Notation "'Exp' a ≈ b ∈ R" := (R a b : (Prop : Type)) (in custom judg at level 90, a custom exp, b custom exp, R constr).
Notation "'EF' a ≈ b ∈ R ↘ R'" := (R R' a b : (Prop : Type)) (in custom judg at level 90, a custom exp, b custom exp, R constr, R' constr).

Generalizable All Variables.

(** Helper Bundles *)
Inductive rel_mod_eval (R : relation domain -> domain -> domain -> Prop) A p A' p' R' : Prop := mk_rel_mod_eval : forall a a', {{ ⟦ A ⟧ p ↘ a }} -> {{ ⟦ A' ⟧ p' ↘ a' }} -> {{ DF a ≈ a' ∈ R ↘ R' }} -> rel_mod_eval R A p A' p' R'.
#[global]
Arguments mk_rel_mod_eval {_ _ _ _ _ _}.

Inductive rel_mod_app (R : relation domain) f a f' a' : Prop := mk_rel_mod_app : forall fa f'a', {{ $| f & a |↘ fa }} -> {{ $| f' & a' |↘ f'a' }} -> {{ Dom fa ≈ f'a' ∈ R }} -> rel_mod_app R f a f' a'.
#[global]
Arguments mk_rel_mod_app {_ _ _ _ _}.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : {{ Dom ~?c ≈ ~?c' ∈ ?in_rel0 }} |- _ =>
        tryif (unify in_rel0 in_rel)
        then (destruct (H _ _ H') as []; destruct_all; mark_with H' 1)
        else fail
    end;
  unmark_all_with 1.
Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    end;
  unmark_all.

(** (Some Elements of) PER Lattice *)

Definition per_bot : relation domain_ne := fun m n => (forall s, exists L, {{ Rne m in s ↘ L }} /\ {{ Rne n in s ↘ L }}).
#[global]
Arguments per_bot /.

Definition per_top : relation domain_nf := fun m n => (forall s, exists L, {{ Rnf m in s ↘ L }} /\ {{ Rnf n in s ↘ L }}).
#[global]
Arguments per_top /.

Definition per_top_typ : relation domain := fun a b => (forall s, exists C, {{ Rtyp a in s ↘ C }} /\ {{ Rtyp b in s ↘ C }}).
#[global]
Arguments per_top_typ /.

Inductive per_nat : relation domain :=
| per_nat_zero : {{ Dom zero ≈ zero ∈ per_nat }}
| per_nat_succ :
  `{ {{ Dom m ≈ n ∈ per_nat }} ->
     {{ Dom succ m ≈ succ n ∈ per_nat }} }
| per_nat_neut :
  `{ {{ Dom m ≈ n ∈ per_bot }} ->
     {{ Dom ⇑ ℕ m ≈ ⇑ ℕ n ∈ per_nat }} }
.

Inductive per_ne : relation domain :=
| per_ne_neut :
  `{ {{ Dom m ≈ m' ∈ per_bot }} ->
     {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_ne }} }
.

(** Universe/Element PER Definition *)

Section Per_univ_elem_core_def.
  Variable
    (i : nat)
      (per_univ_rec : forall {j}, j < i -> relation domain).

  Inductive per_univ_elem_core : relation domain -> domain -> domain -> Prop :=
  | per_univ_elem_core_univ :
    `{ forall (elem_rel : relation domain)
          (lt_j_i : j < i),
          j = j' ->
          (forall a a', elem_rel a a' <-> per_univ_rec lt_j_i a a') ->
          {{ DF 𝕌@j ≈ 𝕌@j' ∈ per_univ_elem_core ↘ elem_rel }} }
  | per_univ_elem_core_nat :
    forall (elem_rel : relation domain),
      (forall m m', elem_rel m m' <-> per_nat m m') ->
      {{ DF ℕ ≈ ℕ ∈ per_univ_elem_core ↘ elem_rel }}
  | per_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
         (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
         (elem_rel : relation domain)
         (equiv_a_a' : {{ DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel}}),
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval per_univ_elem_core B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
          (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app (out_rel equiv_c_c') f c f' c') ->
          {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem_core ↘ elem_rel }} }
  | per_univ_elem_core_neut :
    `{ forall (elem_rel : relation domain),
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (forall m m', elem_rel m m' <-> per_ne m m') ->
          {{ DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ elem_rel }} }
  .

  Hypothesis
    (motive : relation domain -> domain -> domain -> Prop)
      (case_U : forall {j j' elem_rel} (lt_j_i : j < i), j = j' -> (forall a a', elem_rel a a' <-> per_univ_rec lt_j_i a a') -> motive elem_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}})
      (case_nat : forall {elem_rel}, (forall m m', elem_rel m m' <-> per_nat m m') -> motive elem_rel d{{{ ℕ }}} d{{{ ℕ }}})
      (case_Pi :
        forall {A p B A' p' B' in_rel}
           (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
           {elem_rel},
          {{ DF A ≈ A' ∈ per_univ_elem_core ↘ in_rel }} ->
          motive in_rel A A' ->
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_univ_elem_core ↘ R }} /\ motive R x y) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
          (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app (out_rel equiv_c_c') f c f' c') ->
          motive elem_rel d{{{ Π A p B }}} d{{{ Π A' p' B' }}})
      (case_ne : (forall {a b a' b' elem_rel}, {{ Dom b ≈ b' ∈ per_bot }} -> (forall m m', elem_rel m m' <-> per_ne m m') -> motive elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}})).

  #[derive(equations=no, eliminator=no)]
  Equations per_univ_elem_core_strong_ind R a b (H : {{ DF a ≈ b ∈ per_univ_elem_core ↘ R }}) : {{ DF a ≈ b ∈ motive ↘ R }} :=
  | R, a, b, (per_univ_elem_core_univ _ lt_j_i HE eq)                 => case_U lt_j_i HE eq;
  | R, a, b, (per_univ_elem_core_nat _ HE)                            => case_nat HE;
  | R, a, b, (per_univ_elem_core_pi _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi out_rel equiv_a_a' (per_univ_elem_core_strong_ind _ _ _ equiv_a_a') per
        (fun _ _ equiv_c_c' => match HT _ _ equiv_c_c' with
                              | mk_rel_mod_eval b b' evb evb' Rel =>
                                  mk_rel_mod_eval b b' evb evb' (conj _ (per_univ_elem_core_strong_ind _ _ _ Rel))
                              end)
        HE;
  | R, a, b, (per_univ_elem_core_neut _ equiv_b_b' HE)                => case_ne equiv_b_b' HE.

End Per_univ_elem_core_def.

#[export]
Hint Constructors per_univ_elem_core : mcltt.

Equations per_univ_elem (i : nat) : relation domain -> domain -> domain -> Prop by wf i :=
| i => per_univ_elem_core i (fun j lt_j_i a a' => exists R', {{ DF a ≈ a' ∈ per_univ_elem j ↘ R' }}).

Definition per_univ (i : nat) : relation domain := fun a a' => exists R', {{ DF a ≈ a' ∈ per_univ_elem i ↘ R' }}.
#[global]
Arguments per_univ _ _ _ /.

Lemma per_univ_elem_core_univ' : forall j i elem_rel,
    j < i ->
    (forall a a', elem_rel a a' <-> per_univ j a a') ->
    {{ DF 𝕌@j ≈ 𝕌@j ∈ per_univ_elem i ↘ elem_rel }}.
Proof.
  intros.
  simp per_univ_elem.
  apply per_univ_elem_core_univ; try assumption.
  reflexivity.
Qed.
#[export]
Hint Resolve per_univ_elem_core_univ' : mcltt.

(** Universe/Element PER Induction Principle *)

Section Per_univ_elem_ind_def.
  Hypothesis
    (motive : nat -> relation domain -> domain -> domain -> Prop)
      (case_U : forall i {j j' elem_rel},
          j < i -> j = j' ->
          (forall a a', elem_rel a a' <-> per_univ j a a') ->
          (forall A B R, {{ DF A ≈ B ∈ per_univ_elem j ↘ R }} -> motive j R A B) ->
          motive i elem_rel d{{{ 𝕌@j }}} d{{{ 𝕌@j' }}})
      (case_N : forall i {elem_rel},
          (forall m m', elem_rel m m' <-> per_nat m m') ->
          motive i elem_rel d{{{ ℕ }}} d{{{ ℕ }}})
      (case_Pi :
        forall i {A p B A' p' B' in_rel}
           (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation domain)
           {elem_rel},
          {{ DF A ≈ A' ∈ per_univ_elem i ↘ in_rel }} ->
          motive i in_rel A A' ->
          PER in_rel ->
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_univ_elem i ↘ R }} /\ motive i R x y) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
          (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app (out_rel equiv_c_c') f c f' c') ->
          motive i elem_rel d{{{ Π A p B }}} d{{{ Π A' p' B' }}})
      (case_ne : (forall i {a b a' b' elem_rel}, {{ Dom b ≈ b' ∈ per_bot }} -> (forall m m', elem_rel m m' <-> per_ne m m') -> motive i elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}})).

  #[local]
  Ltac def_simp := simp per_univ_elem in *.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind' (i : nat) (R : relation domain) (a b : domain)
    (H : {{ DF a ≈ b ∈ per_univ_elem_core i (fun j lt_j_i a a' => exists R', {{ DF a ≈ a' ∈ per_univ_elem j ↘ R' }}) ↘ R }}) : {{ DF a ≈ b ∈ motive i ↘ R }} by wf i :=
  | i, R, a, b, H =>
      per_univ_elem_core_strong_ind i _ (motive i)
        (fun _ _ _ j_lt_i eq HE => case_U i j_lt_i eq HE (fun A B R' H' => per_univ_elem_ind' _ R' A B _))
        (fun _ => case_N i)
        (fun _ _ _ _ _ _ _ out_rel _ _ IHA per _ => case_Pi i out_rel _ IHA per _)
        (fun _ _ _ _ _ => case_ne i)
        R a b H.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind i a b R (H : per_univ_elem i a b R) : motive i a b R :=
  | i, a, b, R, H := per_univ_elem_ind' i a b R _.
End Per_univ_elem_ind_def.

(** Universe/Element PER Helper Tactics *)

Ltac invert_per_univ_elem H :=
  simp per_univ_elem in H;
  inversion H;
  subst;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac per_univ_elem_econstructor :=
  simp per_univ_elem;
  econstructor;
  try rewrite <- per_univ_elem_equation_1 in *.

(** Context/Environment PER *)

Definition rel_typ (i : nat) (A : typ) (p : env) (A' : typ) (p' : env) R' := rel_mod_eval (per_univ_elem i) A p A' p' R'.
Arguments rel_typ _ _ _ _ _ _ /.

Inductive per_ctx_env : relation env -> ctx -> ctx -> Prop :=
| per_ctx_env_nil :
  `{ forall env_rel,
        (forall p p', env_rel p p' <-> True) ->
        {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }} }
| per_ctx_env_cons :
  `{ forall tail_rel
        (head_rel : forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}), relation domain)
        env_rel
        (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
        PER tail_rel ->
        (forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}),
            rel_typ i A p A' p' (head_rel equiv_p_p')) ->
        (forall p p', env_rel p p' <->
                    exists (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel }}),
                      {{ Dom ~(p 0) ≈ ~(p' 0) ∈ head_rel equiv_p_drop_p'_drop }}) ->
        {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_rel }} }
.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env R' Γ Γ'.
Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.
