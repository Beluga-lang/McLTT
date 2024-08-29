From Mcltt Require Import Base LibTactics.
From Mcltt.Algorithmic Require Export Subtyping.Definitions.
From Mcltt.Core Require Import Soundness Completeness.
From Mcltt.Core.Semantic Require Import NbE.
From Mcltt.Core.Syntactic Require Import System.Definitions.
From Mcltt.Core.Syntactic Require Export Syntax.
Import Domain_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom nf).
Reserved Notation "Γ '⊢a' M ⟸ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
(* Reserved Notation "Γ '⊢a' A @ i" (in custom judg at level 80, Γ custom exp, A custom exp, i constr). *)

Generalizable All Variables.

Inductive alg_type_check : ctx -> typ -> exp -> Prop :=
| atc_ati :
  `( {{ Γ ⊢a M ⟹ A }} ->
     {{ Γ ⊢a A ⊆ B }} ->
     {{ Γ ⊢a M ⟸ B }} )
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope
with alg_type_infer : ctx -> nf -> exp -> Prop :=
| ati_typ :
  `( {{ Γ ⊢a Type@i ⟹ Type@(S i) }} )
| ati_nat :
  `( {{ Γ ⊢a ℕ ⟹ Type@0 }} )
| ati_zero :
  `( {{ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ :
  `( {{ Γ ⊢a M ⟸ ℕ }} ->
     {{ Γ ⊢a succ M ⟹ ℕ }} )
| ati_natrec :
  `( {{ Γ, ℕ ⊢a A ⟹ Type@i }} ->
     {{ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
     {{ Γ, ℕ, A ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
     {{ Γ ⊢a M ⟸ ℕ }} ->
     nbe_ty Γ {{{ A[Id,,M] }}} B ->
     {{ Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ B }} )
| ati_pi :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ, A ⊢a B ⟹ Type@j }} ->
     {{ Γ ⊢a Π A B ⟹ Type@(max i j) }} )
| ati_fn :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ, A ⊢a M ⟹ B }} ->
     nbe_ty Γ A C ->
     {{ Γ ⊢a λ A M ⟹ Π C B }} )
| ati_app :
  `( {{ Γ ⊢a M ⟹ Π A B }} ->
     {{ Γ ⊢a N ⟸ A }} ->
     nbe_ty Γ {{{ B[Id,,N] }}} C ->
     {{ Γ ⊢a M N ⟹ C }} )
| ati_vlookup :
  `( {{ #x : A ∈ Γ }} ->
     nbe_ty Γ A B ->
     {{ Γ ⊢a #x ⟹ B }} )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope.

(* Variant alg_univ_infer : ctx -> nat -> typ -> Prop := *)
(* | aui_ati : *)
(*   `( {{ Γ ⊢a A ⟹ Type@i }} -> *)
(*      {{ Γ ⊢a A @ i }} ) *)
(* where "Γ '⊢a' A @ i" := (alg_univ_infer Γ i A) (in custom judg) : type_scope. *)

#[export]
Hint Constructors alg_type_check alg_type_infer (* alg_univ_infer *) : mcltt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp {{{ Type@i }}} )
| user_exp_nat :
  `( user_exp {{{ ℕ }}} )
| user_exp_zero :
  `( user_exp {{{ zero }}} )
| user_exp_succ :
  `( user_exp {{{ M }}} ->
     user_exp {{{ succ M }}} )
| user_exp_natrec :
  `( user_exp {{{ A }}} ->
     user_exp {{{ MZ }}} ->
     user_exp {{{ MS }}} ->
     user_exp {{{ M }}} ->
     user_exp {{{ rec M return A | zero -> MZ | succ -> MS end }}} )
| user_exp_pi :
  `( user_exp {{{ A }}} ->
     user_exp {{{ B }}} ->
     user_exp {{{ Π A B }}} )
| user_exp_fn :
  `( user_exp {{{ A }}} ->
     user_exp {{{ M }}} ->
     user_exp {{{ λ A M }}} )
| user_exp_app :
  `( user_exp {{{ M }}} ->
     user_exp {{{ N }}} ->
     user_exp {{{ M N }}} )
| user_exp_vlookup :
  `( user_exp {{{ #x }}} ).

#[export]
Hint Constructors user_exp : mcltt.
