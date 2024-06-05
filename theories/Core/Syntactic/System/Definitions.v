From Coq Require Import List Classes.RelationClasses.
Require Import Setoid.
From Mcltt Require Import Base LibTactics.
From Mcltt Require Export Syntax.
Import Syntax_Notations.

Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "⊢ Γ ≈ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢s σ ≈ σ' : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).

Generalizable All Variables.

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `({{ #0 : A[Wk] ∈ Γ , A }})
  | there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A[Wk] ∈ Γ , B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

Inductive wf_ctx : ctx -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ ⊢ Γ , A }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope
with wf_ctx_eq : ctx -> ctx -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Δ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ⊢ A ≈ A' : Type@i }} ->
     {{ ⊢ Γ , A ≈ Δ , A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope
with wf_exp : ctx -> exp -> typ -> Prop :=
| wf_univ :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Type@i : Type@(S i) }} )
| wf_nat :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ ℕ : Type@i }} )
| wf_zero :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ zero : ℕ }} )
| wf_succ :
  `( {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ succ M : ℕ }} )
| wf_natrec :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )
| wf_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ Π A B : Type@i }} )
| wf_fn :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ M : B }} ->
     {{ Γ ⊢ λ A M : Π A B }} )
| wf_app :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ M N : B[Id,,N] }} )
| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )
| wf_exp_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ M : A }} ->
     {{ Γ ⊢ M[σ] : A[σ] }} )
| wf_conv :
  `( {{ Γ ⊢ M : A }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ ⊢ M : A' }} )
| wf_cumu :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A : Type@(S i) }} )
where "Γ ⊢ M : A" := (wf_exp Γ M A) (in custom judg) : type_scope
with wf_sub : ctx -> sub -> ctx -> Prop :=
| wf_sub_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id : Γ }} )
| wf_sub_weaken :
  `( {{ ⊢ Γ , A }} ->
     {{ Γ , A ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢s (σ ,, M) : Δ , A }} )
| wf_sub_conv :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ ⊢s σ : Δ' }} )
where "Γ ⊢s σ : Δ" := (wf_sub Γ σ Δ) (in custom judg) : type_scope
with wf_exp_eq : ctx -> typ -> exp -> exp -> Prop :=
| wf_exp_eq_typ_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@(S i) }} )
| wf_exp_eq_nat_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@i }} )
| wf_exp_eq_zero_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ zero[σ] ≈ zero : ℕ }} )
| wf_exp_eq_succ_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ M : ℕ }} ->
     {{ Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ }} )
| wf_exp_eq_succ_cong :
  `( {{ Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Γ ⊢ succ M ≈ succ M' : ℕ }} )
| wf_exp_eq_natrec_cong :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ , ℕ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_natrec_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ , ℕ ⊢ A : Type@i }} ->
     {{ Δ ⊢ MZ : A[Id,,zero] }} ->
     {{ Δ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
     {{ Δ ⊢ M : ℕ }} ->
     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} )
| wf_exp_eq_nat_beta_zero :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
     {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( {{ Γ , ℕ ⊢ A : Type@i }} ->
     {{ Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Γ , ℕ , A ⊢ MS : A[Wk∘Wk,,succ(#1)] }} ->
     {{ Γ ⊢ M : ℕ }} ->
     {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )
| wf_exp_eq_pi_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@i }} )
| wf_exp_eq_pi_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ B ≈ B' : Type@i }} ->
     {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }} )
| wf_exp_eq_fn_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ M ≈ M' : B }} ->
     {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }} )
| wf_exp_eq_fn_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ , A ⊢ M : B }} ->
     {{ Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : Π A B }} ->
     {{ Γ ⊢ N ≈ N' : A }} ->
     {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ , A ⊢ B : Type@i }} ->
     {{ Δ ⊢ M : Π A B }} ->
     {{ Δ ⊢ N : A }} ->
     {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ , A ⊢ M : B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }} )
| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x ≈ #x : A }} )
| wf_exp_eq_var_0_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢ #0[σ ,, M] ≈ M : A[σ] }} )
| wf_exp_eq_var_S_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ #x : B ∈ Δ }} ->
     {{ Γ ⊢ #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Γ , B }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ , B ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )
| wf_exp_eq_sub_cong :
  `( {{ Δ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_id :
  `( {{ Γ ⊢ M : A }} ->
     {{ Γ ⊢ M[Id] ≈ M : A }} )
| wf_exp_eq_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ M : A }} ->
     {{ Γ ⊢ M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }} )
| wf_exp_eq_cumu :
  `( {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@(S i) }} )
| wf_exp_eq_conv :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M'' : A }} ->
     {{ Γ ⊢ M ≈ M'' : A }} )
where "Γ ⊢ M ≈ M' : A" := (wf_exp_eq Γ A M M') (in custom judg) : type_scope

with wf_sub_eq : ctx -> ctx -> sub -> sub -> Prop :=
| wf_sub_eq_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ ⊢ Γ , A }} ->
     {{ Γ , A ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Γ ⊢s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Γ ⊢s (σ ,, M) ≈ (σ' ,, M') : Δ , A }} )
| wf_sub_eq_id_compose_right :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢s Id ∘ σ ≈ σ : Δ }} )
| wf_sub_eq_id_compose_left :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢s σ ∘ Id ≈ σ : Δ }} )
| wf_sub_eq_compose_assoc :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ'' ⊢s σ' : Γ' }} ->
     {{ Γ''' ⊢s σ'' : Γ'' }} ->
     {{ Γ''' ⊢s (σ ∘ σ') ∘ σ'' ≈ σ ∘ (σ' ∘ σ'') : Γ }} )
| wf_sub_eq_extend_compose :
  `( {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A : Type@i }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ ⊢s (σ ,, M) ∘ τ ≈ ((σ ∘ τ) ,, M[τ]) : Γ'' , A }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ' ⊢s Wk ∘ (σ ,, M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ , A }} ->
     {{ Γ' ⊢s σ ≈ ((Wk ∘ σ) ,, #0[σ]) : Γ , A }} )
| wf_sub_eq_sym :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ : Δ }} )
| wf_sub_eq_trans :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ'' : Δ }} ->
     {{ Γ ⊢s σ ≈ σ'' : Δ }} )
| wf_sub_eq_conv :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ' }} )
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ Δ S1 S2) (in custom judg) : type_scope.

Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_eq_mut_ind := Induction for wf_ctx_eq Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop.

#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_exp wf_sub wf_exp_eq wf_sub_eq ctx_lookup: mcltt.

#[export]
  Instance WfExpPER Γ A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
  Instance WfSubPER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.


Add Parametric Morphism i Γ : (wf_exp Γ)
    with signature eq ==> wf_exp_eq Γ {{{ Type@i }}} ==> iff as wf_exp_morph.
Proof.
  intros; split; mauto.
Qed.

Add Parametric Morphism i Γ : (wf_exp_eq Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as wf_exp_eq_morph.
Proof.
  intros; split; mauto.
Qed.

#[export]
  Hint Rewrite -> wf_exp_eq_typ_sub wf_exp_eq_nat_sub wf_exp_eq_pi_sub : mcltt.
