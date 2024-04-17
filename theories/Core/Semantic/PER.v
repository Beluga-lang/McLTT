From Coq Require Import Lia PeanoNat Relations Program.Wf.
From Mcltt Require Import Base Domain Evaluate Readback Syntax System.

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
          (out_rel : forall {c c'}, {{ Dom c ≈ c' ∈ in_rel }} -> relation domain)
          (equiv_a_a' : {{ DF a ≈ a' ∈ per_univ_elem_core ↘ in_rel}}),
          (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_mod_eval per_univ_elem_core B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel equiv_c_c')) ->
          (elem_rel = fun f f' => forall {c c'} (equiv_c_c' : in_rel c c'),
                          rel_mod_app (out_rel equiv_c_c') f c f' c') ->
          {{ DF Π a p B ≈ Π a' p' B' ∈ per_univ_elem_core ↘ elem_rel }} }
  | per_univ_elem_core_neut :
    `{ {{ DF ⇑ a b ≈ ⇑ a' b' ∈ per_univ_elem_core ↘ per_ne }} }
  .
End Per_univ_elem_core_def.

Global Hint Constructors per_univ_elem_core : mcltt.

Definition per_univ_like (R : domain -> domain -> relation domain -> Prop) := fun a a' => exists R', {{ DF a ≈ a' ∈ R ↘ R' }}.
#[global]
Transparent per_univ_like.

Program Fixpoint per_univ_elem (i : nat) {wf lt i} : domain -> domain -> relation domain -> Prop := Per_univ_def.per_univ_elem i (fun _ lt_j_i => per_univ_like (per_univ_elem _ lt_j_i)).
Definition per_univ (i : nat) : relation domain := per_univ_like (per_univ_elem i).

Definition rel_typ (i : nat) (A : typ) (p : env) (A' : typ) (p' : env) R' := rel_mod_eval (per_univ_elem i) A p A' p' R'.

Inductive per_ctx_env : ctx -> ctx -> relation env -> Prop :=
| per_ctx_env_nil :
  `{ (Env = fun p p' => True) ->
     {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ Env }} }
| per_ctx_env_cons :
  `{ forall (tail_rel : relation env)
        (head_rel : forall {p p'}, {{ Dom p ≈ p' ∈ tail_rel }} -> relation domain)
        (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }})
        (rel_A_A' : forall {p p'} (equiv_p_p' : {{ Dom p ≈ p' ∈ tail_rel }}), rel_typ i A p A' p' (head_rel equiv_p_p')),
        (Env = fun p p' => exists (equiv_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ tail_rel }}),
                   {{ Dom ~(p 0) ≈ ~(p' 0) ∈ head_rel equiv_p_drop_p'_drop }}) ->
        {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ Env }} }
.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env Γ Γ' R'.
Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.
