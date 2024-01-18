From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base Domain Evaluate Readback Syntax System.

Notation "'Dom' a ≈ b ∈ R" := (R a b) (in custom judg at level 90, a custom domain, b custom domain, R constr, only parsing).
Notation "'Exp' a ≈ b ∈ R" := (R a b) (in custom judg at level 90, a custom exp, b custom exp, R constr, only parsing).

Generalizable All Variables.

Record rel_mod_eval_R R A p A' p' := mk_rel_mod_eval_R
  { rel_mod_eval_R_a : domain
  ; rel_mod_eval_R_a' : domain
  ; rel_mod_eval_R_eval_A : {{ ⟦ A ⟧ p ↘ rel_mod_eval_R_a }}
  ; rel_mod_eval_R_eval_A' : {{ ⟦ A' ⟧ p' ↘ rel_mod_eval_R_a' }}
  ; rel_mod_eval_R_eq : {{ Dom rel_mod_eval_R_a ≈ rel_mod_eval_R_a' ∈ R }}
  }
.  

Arguments rel_mod_eval_R_a {_} {_} {_} {_} {_} _.
Arguments rel_mod_eval_R_a' {_} {_} {_} {_} {_} _.
Arguments rel_mod_eval_R_eval_A {_} {_} {_} {_} {_} _.
Arguments rel_mod_eval_R_eval_A' {_} {_} {_} {_} {_} _.
Arguments rel_mod_eval_R_eq {_} {_} {_} {_} {_} _.

Record rel_mod_app_R R f a f' a' := mk_rel_mod_app_R
  { rel_mod_app_R_fa : domain
  ; rel_mod_app_R_f'a' : domain
  ; rel_mod_app_R_app_fa : {{ $| f & a |↘ rel_mod_app_R_fa }}
  ; rel_mod_app_R_app_f'a' : {{ $| f' & a'|↘ rel_mod_app_R_f'a' }}
  ; rel_mod_app_R_eq : {{ Dom rel_mod_app_R_fa ≈ rel_mod_app_R_f'a' ∈ R }}
  }
.

Arguments rel_mod_app_R_fa {_} {_} {_} {_} {_} _.
Arguments rel_mod_app_R_f'a' {_} {_} {_} {_} {_} _.
Arguments rel_mod_app_R_app_fa {_} {_} {_} {_} {_} _.
Arguments rel_mod_app_R_app_f'a' {_} {_} {_} {_} {_} _.
Arguments rel_mod_app_R_eq {_} {_} {_} {_} {_} _.

Definition per_bot : relation domain_ne := fun m n => (forall s, exists L, {{ Rne m in s ↘ L }} /\ {{ Rne n in s ↘ L }}).

Definition per_top : relation domain_nf := fun m n => (forall s, exists L, {{ Rnf m in s ↘ L }} /\ {{ Rnf n in s ↘ L }}).

Definition per_top_typ : relation domain := fun a b => (forall s, exists C, {{ Rtyp a in s ↘ C }} /\ {{ Rtyp b in s ↘ C }}).

Inductive per_nat : relation domain :=
| per_nat_zero : {{ Dom zero ≈ zero ∈ per_nat }}
| per_nat_succ :
  `( {{ Dom m ≈ n ∈ per_nat }} ->
     {{ Dom succ m ≈ succ n ∈ per_nat }} )
| per_nat_neut :
  `( {{ Dom m ≈ n ∈ per_bot }} ->
     {{ Dom ⇑ ℕ m ≈ ⇑ ℕ n ∈ per_nat }} )
.

Inductive per_ne : relation domain :=
| per_ne_neut :
  `( {{ Dom m ≈ n ∈ per_bot }} ->
     {{ Dom ⇑ a m ≈ ⇑ a' n ∈ per_ne }} )
.

Module Per_univ_def.
  Section Per_univ_def.
    Variable (i : nat) (per_univ_rec : forall {j}, j < i -> relation domain).

    Inductive per_univ_template : relation domain :=
    | per_univ_template_univ :
      `{ j < i ->
         j = j' ->
         {{ Dom 𝕌@j ≈ 𝕌@j' ∈ per_univ_template }} }
    | per_univ_template_nat : {{ Dom ℕ ≈ ℕ ∈ per_univ_template }}
    | per_univ_template_pi :
      `{ forall (univ_rel : relation domain)
            (elem_rel : forall {c c'}, {{ Dom c ≈ c' ∈ univ_rel }} -> relation domain)
            (eq_a_a' : {{ Dom a ≈ a' ∈ univ_rel }}),
            (forall {c c'},
                {{ Dom c ≈ c' ∈ elem_rel eq_a_a' }} ->
                rel_mod_eval_R per_univ_template B d{{{ p ↦ c }}} B' d{{{ p ↦ c' }}}) ->
            {{ Dom Π a p B ≈ Π a' p' B' ∈ per_univ_template }} }
    | per_univ_template_neut :
      `{ {{ Dom m ≈ m' ∈ per_bot }} ->
         {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_univ_template }} }
    .

    Inductive per_elem_template : forall {a a'}, per_univ_template a a' -> relation domain :=
    | per_elem_template_univ :
      `{ forall (eq : j = j'),
            {{ Dom b ≈ b' ∈ @per_univ_rec j lt_j_i }} ->
            {{ Dom b ≈ b' ∈ per_elem_template (per_univ_template_univ lt_j_i eq) }} }
    | per_elem_template_nat :
      `{ {{ Dom m ≈ m' ∈ per_nat }} ->
         {{ Dom m ≈ m' ∈ per_elem_template per_univ_template_nat }} }
    | per_elem_template_pi :
      `{ forall (univ_rel : relation domain)
            (elem_rel : forall {c c'}, {{ Dom c ≈ c' ∈ univ_rel }} -> relation domain)
            (eq_a_a' : {{ Dom a ≈ a' ∈ univ_rel }})
            (rel_B_B' : forall {c c'},
                {{ Dom c ≈ c' ∈ elem_rel eq_a_a' }} ->
                rel_mod_eval_R per_univ_template B d{{{ p ↦ c }}} B' d{{{ p ↦ c' }}}),
            (forall {c c'} (eq_c_c' : {{ Dom c ≈ c' ∈ elem_rel eq_a_a' }}),
                rel_mod_app_R (per_elem_template (rel_mod_eval_R_eq (rel_B_B' eq_c_c'))) f c f' c') ->
            {{ Dom f ≈ f' ∈ per_elem_template (@per_univ_template_pi a a' B p B' p' univ_rel (@elem_rel) eq_a_a' (@rel_B_B')) }} }
    | per_elem_template_neut :
      `{ forall (eq_a_a' : {{ Dom a ≈ a' ∈ per_bot }}),
            {{ Dom m ≈ m' ∈ per_ne }} ->
            {{ Dom m ≈ m' ∈ per_elem_template (@per_univ_template_neut a a' b b' eq_a_a') }} }
    .

    Inductive per_univ_check : forall {m m'}, per_univ_template m m' -> Prop :=
    | per_univ_check_univ :
      `{ per_univ_check (@per_univ_template_univ j j' lt_j_i eq_j_j') }
    | per_univ_check_nat : per_univ_check per_univ_template_nat
    | per_univ_check_pi :
      `{ forall (eq_a_a' : {{ Dom a ≈ a' ∈ per_univ_template }})
            (rel_B_B' : forall {c c'},
                {{ Dom c ≈ c' ∈ per_elem_template eq_a_a' }} ->
                rel_mod_eval_R per_univ_template B d{{{ p ↦ c }}} B' d{{{ p ↦ c' }}}),
            per_univ_check eq_a_a' ->
            (forall {c c'}
                (eq_c_c' : {{ Dom c ≈ c' ∈ per_elem_template eq_a_a' }}),
                per_univ_check (rel_mod_eval_R_eq (rel_B_B' eq_c_c'))) ->
            per_univ_check (@per_univ_template_pi a a' B p B' p' per_univ_template (@per_elem_template) eq_a_a' (@rel_B_B')) }
    | per_univ_check_neut :
      `{ per_univ_check (@per_univ_template_neut m m' a a' eq_m_m') }
    .

    Definition per_univ : relation domain := fun a a' => exists (eq_a_a' : per_univ_template a a'), per_univ_check eq_a_a'.

    Definition per_elem {a a'} (eq_a_a' : per_univ a a') : relation domain := per_elem_template (ex_proj1 eq_a_a').
  End Per_univ_def.
End Per_univ_def.

Fixpoint per_univ_base (i : nat) {j} (lt_j_i : j < i) : relation domain.
Proof.
  destruct i.
  - contradiction (Nat.nlt_0_r _ lt_j_i).
  - apply Per_univ_def.per_univ with j.
    intros k lt_k_j.
    eapply per_univ_base with (i := i).
    eapply Nat.lt_le_trans.
    + exact lt_k_j.
    + eapply le_S_n; assumption.
Defined.

Definition per_univ (i : nat) : relation domain := Per_univ_def.per_univ i (@per_univ_base i).
Definition per_elem {i a a'} (eq_a_a' : {{ Dom a ≈ a' ∈ per_univ i }}) : relation domain := Per_univ_def.per_elem i (@per_univ_base i) eq_a_a'.

Definition rel_typ (i : nat) (A : typ) (p : env) (A' : typ) (p' : env) := rel_mod_eval_R (per_univ i) A p A' p'.

Module Per_ctx_def.
  Inductive per_ctx_template : relation ctx :=
  | per_ctx_template_nil : {{ Exp ⋅ ≈ ⋅ ∈ per_ctx_template }}
  | per_ctx_template_cons :
    `{ forall (ctx_rel : relation ctx)
          (env_rel : forall {Γ Γ'}, {{ Exp Γ ≈ Γ' ∈ ctx_rel }} -> relation env)
          (eq_Γ_Γ' : {{ Exp Γ ≈ Γ' ∈ ctx_rel }}),
          (forall {p p'}, {{ Dom p ≈ p' ∈ env_rel eq_Γ_Γ' }} -> rel_typ i A p A' p') ->
          {{ Exp Γ, A ≈ Γ', A' ∈ per_ctx_template }} }
  .

  Inductive per_env_template : forall {Γ Γ'}, per_ctx_template Γ Γ' -> relation env :=
  | per_env_template_nil :
    `{ {{ Dom p ≈ p ∈ per_env_template per_ctx_template_nil }} }
  | per_env_template_cons :
    `{ forall (ctx_rel : relation ctx)
          (env_rel : forall {Γ Γ'}, {{ Exp Γ ≈ Γ' ∈ ctx_rel }} -> relation env)
          (eq_Γ_Γ' : {{ Exp Γ ≈ Γ' ∈ ctx_rel }})
          (rel_A_A' : forall {p p'}, {{ Dom p ≈ p' ∈ env_rel eq_Γ_Γ' }} -> rel_typ i A p A' p')
          (eq_p_drop_p'_drop : {{ Dom p ↯ ≈ p' ↯ ∈ env_rel eq_Γ_Γ' }}),
          {{ Dom ~(p 0) ≈ ~(p' 0) ∈ per_elem (rel_mod_eval_R_eq (rel_A_A' eq_p_drop_p'_drop)) }} ->
          {{ Dom p ≈ p ∈ per_env_template (per_ctx_template_cons ctx_rel (@env_rel) eq_Γ_Γ' (@rel_A_A')) }} }
  .

  Inductive per_ctx_check : forall {Γ Γ'}, per_ctx_template Γ Γ' -> Prop :=
  | per_ctx_check_nil : per_ctx_check per_ctx_template_nil
  | per_ctx_check_cons :
    `{ forall (eq_Γ_Γ' : {{ Exp Γ ≈ Γ' ∈ per_ctx_template }})
          (rel_A_A' : forall {p p'}, {{ Dom p ≈ p' ∈ per_env_template eq_Γ_Γ' }} -> rel_typ i A p A' p'),
          per_ctx_check eq_Γ_Γ' ->
          per_ctx_check (per_ctx_template_cons per_ctx_template (@per_env_template) eq_Γ_Γ' (@rel_A_A')) }
  .
End Per_ctx_def.

Definition per_ctx : relation ctx := fun Γ Γ' => exists (eq_Γ_Γ' : Per_ctx_def.per_ctx_template Γ Γ'), Per_ctx_def.per_ctx_check eq_Γ_Γ'.

Definition per_env {Γ Γ'} (eq_Γ_Γ' : Per_ctx_def.per_ctx_template Γ Γ') : relation env := Per_ctx_def.per_env_template eq_Γ_Γ'.

Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.