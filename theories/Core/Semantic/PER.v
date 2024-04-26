From Coq Require Import Lia PeanoNat Relations.
<<<<<<< HEAD
=======
From Equations Require Import Equations.

>>>>>>> 47fa52f5eb989104966e70555de900ab7ce0e164
From Mcltt Require Import Base Domain Evaluate Readback Syntax System.
From Equations Require Import Equations.

Definition in_dom_rel {A} (R : relation A) := R.
Definition in_dom_fun_rel {A} {B} (R : A -> A -> relation B -> Prop) := R.
Definition in_exp_rel {A} (R : relation A) := R.
Definition in_exp_fun_rel {A} {B} (R : A -> A -> relation B -> Prop) := R.

Notation "'Dom' a ≈ b ∈ R" := (in_dom_rel R a b) (in custom judg at level 90, a custom domain, b custom domain, R constr).
Notation "'DF' a ≈ b ∈ R ↘ R'" := (in_dom_fun_rel R a b R') (in custom judg at level 90, a custom domain, b custom domain, R constr, R' constr).
Notation "'Exp' a ≈ b ∈ R" := (in_exp_rel R a b) (in custom judg at level 90, a custom exp, b custom exp, R constr).
Notation "'EF' a ≈ b ∈ R ↘ R'" := (in_exp_fun_rel R a b R') (in custom judg at level 90, a custom exp, b custom exp, R constr, R' constr).

Generalizable All Variables.

Inductive rel_mod_eval (R : domain -> domain -> relation domain -> Prop) A p A' p' R' : Prop := mk_rel_mod_eval : forall a a', {{ ⟦ A ⟧ p ↘ a }} -> {{ ⟦ A' ⟧ p' ↘ a' }} -> {{ DF a ≈ a' ∈ R ↘ R' }} -> rel_mod_eval R A p A' p' R'.
Arguments mk_rel_mod_eval {_ _ _ _ _ _}.

Inductive rel_mod_app (R : relation domain) f a f' a' : Prop := mk_rel_mod_app : forall fa f'a', {{ $| f & a |↘ fa }} -> {{ $| f' & a' |↘ f'a' }} -> {{ Dom fa ≈ f'a' ∈ R }} -> rel_mod_app R f a f' a'.
Arguments mk_rel_mod_app {_ _ _ _ _}.

Definition per_bot : relation domain_ne := fun m n => (forall s, exists L, {{ Rne m in s ↘ L }} /\ {{ Rne n in s ↘ L }}).

Definition per_top : relation domain_nf := fun m n => (forall s, exists L, {{ Rnf m in s ↘ L }} /\ {{ Rnf n in s ↘ L }}).

Definition per_top_typ : relation domain := fun a b => (forall s, exists C, {{ Rtyp a in s ↘ C }} /\ {{ Rtyp b in s ↘ C }}).

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

Section Per_univ_elem_core_def.
  Variable (i : nat) (per_univ_rec : forall {j}, j < i -> relation domain).

  Inductive per_univ_elem_core : domain -> domain -> relation domain -> Prop :=
  | per_univ_elem_core_univ :
    `{ forall (lt_j_i : j < i),
          j = j' ->
          {{ DF 𝕌@j ≈ 𝕌@j' ∈ per_univ_elem_core ↘ per_univ_rec lt_j_i }} }
  | per_univ_elem_core_nat : {{ DF ℕ ≈ ℕ ∈ per_univ_elem_core ↘ per_nat }}
  | per_univ_elem_core_pi :
    `{ forall (in_rel : relation domain)
<<<<<<< HEAD
         (out_rel : forall {c c'}, {{ Dom c ≈ c' ∈ in_rel }} -> relation domain)
         (equiv_a_a' : {{ DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel}}),
=======
          (out_rel : forall {c c'}, {{ Dom c ≈ c' ∈ in_rel }} -> relation domain)
          (equiv_a_a' : {{ DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel }}),
>>>>>>> 47fa52f5eb989104966e70555de900ab7ce0e164
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval per_univ_elem_core B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
          (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : in_rel c c'),
                rel_mod_app (out_rel equiv_c_c') f c f' c') ->
          {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem_core ↘ elem_rel }} }
  | per_univ_elem_core_neut :
    `{ {{ DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ per_ne }} }
  .

  Hypothesis
    (motive : domain -> domain -> relation domain -> Prop).

  Hypothesis
    (case_U : forall (j j' : nat) (lt_j_i : j < i), j = j' -> motive d{{{ 𝕌 @ j}}} d{{{ 𝕌 @ j'}}} (per_univ_rec lt_j_i)).

  Hypothesis
    (case_nat : motive d{{{ ℕ}}} d{{{ ℕ}}} per_nat).

  Hypothesis
    (case_Pi :
      forall {A p B A' p' B' in_rel elem_rel}
        (out_rel : forall c c' : domain, {{ Dom c ≈ c' ∈ in_rel }} -> relation domain),
        {{ DF A ≈ A' ∈ per_univ_elem_core ↘ in_rel }} ->
        motive A A' in_rel ->
        (forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
            rel_mod_eval (fun x y z => per_univ_elem_core x y z /\ motive x y z) B d{{{ p ↦ c}}} B' d{{{ p' ↦ c'}}} (out_rel c c' equiv_c_c')) ->
        (forall f1 f' : domain,
            elem_rel f1 f' <-> (forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app (out_rel c c' equiv_c_c') f1 c f' c')) ->
        motive d{{{ Π A p B}}} d{{{ Π A' p' B'}}} elem_rel).

  Hypothesis
    (case_ne : (forall {a b a' b'}, motive d{{{ ⇑ a b}}} d{{{ ⇑ a' b'}}} per_ne)).

  #[derive(equations=no, eliminator=no)]
  Equations per_univ_elem_core_strong_ind a b R (H : per_univ_elem_core a b R) : motive a b R :=
    per_univ_elem_core_strong_ind a b R (per_univ_elem_core_univ lt_j_i eq) := case_U _ _ lt_j_i eq;
    per_univ_elem_core_strong_ind a b R per_univ_elem_core_nat := case_nat;
    per_univ_elem_core_strong_ind a b R
      (per_univ_elem_core_pi in_rel out_rel equiv_a_a' HT HE) :=
      case_Pi out_rel equiv_a_a' (per_univ_elem_core_strong_ind _ _ _ equiv_a_a')
        (fun _ _ equiv_c_c' => match HT _ _ equiv_c_c' with
                            | mk_rel_mod_eval b b' evb evb' Rel =>
                                mk_rel_mod_eval b b' evb evb' (conj Rel (per_univ_elem_core_strong_ind _ _ _ Rel))
                            end)
        HE;
    per_univ_elem_core_strong_ind a b R per_univ_elem_core_neut :=  case_ne.

End Per_univ_elem_core_def.

Global Hint Constructors per_univ_elem_core : mcltt.

Equations per_univ_elem (i : nat) : domain -> domain -> relation domain -> Prop by wf i :=
| i => per_univ_elem_core i (fun j lt_j_i a a' => exists R', per_univ_elem j a a' R').
<<<<<<< HEAD

Definition per_univ (i : nat) : relation domain := fun a a' => exists R', per_univ_elem i a a' R'.

Lemma per_univ_elem_core_univ' : forall j i,
    j < i ->
    {{ DF 𝕌@j ≈ 𝕌@j ∈ per_univ_elem i ↘ per_univ j }}.
Proof.
  intros.
  simp per_univ_elem.
  unfold per_univ.
  eapply (per_univ_elem_core_univ i (fun j lt_j_i a a' => exists R', per_univ_elem j a a' R') H).
  reflexivity.
Qed.
Global Hint Resolve per_univ_elem_core_univ' : mcltt.

Section Per_univ_elem_ind_def.

  Hypothesis
    (motive : nat -> domain -> domain -> relation domain -> Prop).

  Hypothesis
    (case_U : forall j j' i, j < i -> j = j' ->
                        (forall A B R, per_univ_elem j A B R -> motive j A B R) ->
                        motive i d{{{𝕌@j}}} d{{{𝕌@j'}}} (per_univ j)).

  Hypothesis
    (case_N : forall i, motive i d{{{ℕ}}} d{{{ℕ}}} per_nat).

  Hypothesis
    (case_Pi : forall i {A p B A' p' B' in_rel elem_rel}
                 (out_rel : forall {c c'}, {{ Dom c ≈ c' ∈ in_rel }} -> relation domain),
        {{ DF A ≈ A' ∈ per_univ_elem i ↘ in_rel}} ->
        motive i A A' in_rel ->
        (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
            rel_mod_eval (fun x y z => per_univ_elem i x y z /\ motive i x y z) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
        (forall f f', elem_rel f f' <-> forall {c c'} (equiv_c_c' : in_rel c c'),
                rel_mod_app (out_rel equiv_c_c') f c f' c') ->
        motive i d{{{Π A p B}}} d{{{Π A' p' B'}}} elem_rel).

  Hypothesis
    (case_ne : (forall i {a b a' b'}, motive i d{{{ ⇑ a b}}} d{{{ ⇑ a' b'}}} per_ne)).

  #[local]
   Ltac def_simp := simp per_univ_elem in *.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind' (i : nat) (a b : domain) (R : relation domain)
    (H : per_univ_elem_core i (fun j lt_j_i a a' => exists R', per_univ_elem j a a' R') a b R) : motive i a b R by wf i :=
    per_univ_elem_ind' i a b R H :=
      per_univ_elem_core_strong_ind i _ (motive i)
        (fun j j' j_lt_i eq => case_U j j' i j_lt_i eq (fun A B R' H' => per_univ_elem_ind' _ A B R' _))
        (case_N i)
        (fun A p B A' p' B' in_rel elem_rel out_rel HA IHA IHE HE => case_Pi i out_rel _ _ _ _)
        (@case_ne i)
        a b R H.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind i a b R (H : per_univ_elem i a b R) : motive i a b R :=
    per_univ_elem_ind i a b R H := per_univ_elem_ind' i a b R _.

End Per_univ_elem_ind_def.


Definition per_univ_like (R : domain -> domain -> relation domain -> Prop) := fun a a' => exists R', {{ DF a ≈ a' ∈ R ↘ R' }}.
#[global]
Transparent per_univ_like.

=======
Definition per_univ (i : nat) : relation domain := fun a a' => exists R', per_univ_elem i a a' R'.

>>>>>>> 47fa52f5eb989104966e70555de900ab7ce0e164
Definition rel_typ (i : nat) (A : typ) (p : env) (A' : typ) (p' : env) R' := rel_mod_eval (per_univ_elem i) A p A' p' R'.

Inductive per_ctx_env : ctx -> ctx -> relation env -> Prop :=
| per_ctx_env_nil :
  `{ (Env = fun p p' => True) ->
     {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ Env }} }
| per_ctx_env_cons :
  `{ forall (tail_rel : relation env)
        (head_rel : forall {p p'}, {{ Dom p ≈ p' ∈ tail_rel }} -> relation domain)
        (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
        (forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}), rel_typ i A p A' p' (head_rel equiv_p_p')) ->
        (Env = fun p p' => exists (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel }}),
                   {{ Dom ~(p 0) ≈ ~(p' 0) ∈ head_rel equiv_p_drop_p'_drop }}) ->
        {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ Env }} }
.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env Γ Γ' R'.
Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.
