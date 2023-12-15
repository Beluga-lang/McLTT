Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.
Require Import Mcltt.LibTactics.

#[global] Declare Custom Entry judg.
Notation "{{ x }}" := x (at level 0, x custom judg at level 99, format "'{{'  x  '}}'").
Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "⊢ Γ ≈ Δ" (in custom judg at level 80, Γ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢ A ≈ B : T" (in custom judg at level 80, Γ custom exp, A custom exp, B custom exp, T custom exp).
Reserved Notation "Γ ⊢ t : T" (in custom judg at level 80, Γ custom exp, t custom exp, T custom exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢s S1 ≈ S2 : Δ" (in custom judg at level 80, Γ custom exp, S1 custom exp, S2 custom exp, Δ custom exp).
Reserved Notation "'#' x : T ∈ Γ" (in custom judg at level 80, x constr at level 0, T custom exp, Γ custom exp at level 50).

Generalizable All Variables.

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `({{ #0 : T[Wk] ∈ Γ , T }})
  | there : `({{ #n : T ∈ Γ }} -> {{ #(S n) : T[Wk] ∈ Γ , T' }})
where "'#' x : T ∈ Γ" := (ctx_lookup x T Γ) (in custom judg) : type_scope.

Inductive wf_ctx : ctx -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ T : Type@i }} ->
     {{ ⊢ Γ , T }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope
with wf_ctx_eq : ctx -> ctx -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ T : Type@i }} ->
     {{ Δ ⊢ T' : Type@i }} ->
     {{ Γ ⊢ T ≈ T' : Type@i }} ->
     {{ Δ ⊢ T ≈ T' : Type@i }} ->
     {{ ⊢ Γ , T ≈ Δ , T' }} )
where "⊢ Γ ≈ Δ" := (wf_ctx_eq Γ Δ) (in custom judg) : type_scope
with wf_exp : ctx -> exp -> typ -> Prop :=
| wf_nat :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ ℕ : Type@i }} )
| wf_univ :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Type@i : Type@(S i) }} )
| wf_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ Π A B : Type@i }} )
| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     {{ #x : T ∈ Γ }} ->
     {{ Γ ⊢ #x : T }} )
| wf_app :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ M N : B[Id,,N] }} )
| wf_fn :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ , A ⊢ M : B }} ->
     {{ Γ ⊢ λ A M : Π A B }} )
| wf_zero :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ zero : ℕ }} )
| wf_succ :
  `( {{ Γ ⊢ n : ℕ }} ->
     {{ Γ ⊢ succ n : ℕ }} )
| wf_exp_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ M : A }} ->
     {{ Γ ⊢ M[σ] : A[σ] }} )
| wf_conv :
  `( {{ Γ ⊢ t : T }} ->
     {{ Γ ⊢ T ≈ T' : Type@i }} ->
     {{ Γ ⊢ t : T' }} )
| wf_cumu :
  `( {{ Γ ⊢ T : Type@i }} ->
     {{ Γ ⊢ T : Type@(S i) }} )
where "Γ ⊢ t : T" := (wf_exp Γ t T) (in custom judg) : type_scope
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
with wf_eq : ctx -> exp -> exp -> typ -> Prop :=
| wf_eq_nat_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@i }} )
| wf_eq_typ_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@(S i) }} )
| wf_eq_pi_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ T' : Type@i }} ->
     {{ Δ , T' ⊢ T : Type@i }} ->
     {{ Γ ⊢ (Π T' T)[σ] ≈ Π (T'[σ]) (T[σ ∘ Wk ,, #0]) : Type@i }} )
| wf_eq_pi_cong :
  `( {{ Γ ⊢ M : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : Type@i }} ->
     {{ Γ , M ⊢ T ≈ T' : Type@i }} ->
     {{ Γ ⊢ Π M T ≈ Π M' T' : Type@i }} )
| wf_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : T ∈ Γ }} ->
     {{ Γ ⊢ #x ≈ #x : T }} )
| wf_eq_zero :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ zero ≈ zero : ℕ }} )
| wf_eq_zero_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ zero[σ] ≈ zero : ℕ }} )
| wf_eq_succ_cong :
  `( {{ Γ ⊢ t ≈ t' : ℕ }} ->
     {{ Γ ⊢ succ t ≈ succ t' : ℕ }} )
| wf_eq_succ_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ t : ℕ }} ->
     {{ Γ ⊢ (succ t)[σ] ≈ succ (t[σ]) : ℕ }} )
| wf_eq_exp_sub_cong :
  `( {{ Δ ⊢ t ≈ t' : T }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢ t[σ] ≈ t'[σ'] : T[σ] }} )
| wf_eq_exp_sub_id :
  `( {{ Γ ⊢ t : T }} ->
     {{ Γ ⊢ t[Id] ≈ t : T }} )
| wf_eq_exp_sub_weaken :
  `( {{ ⊢ Γ , M }} ->
     {{ #x : T ∈ Γ }} ->
     {{ Γ , M ⊢ (#x)[Wk] ≈ #(S x) : T[Wk] }} )
| wf_eq_exp_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ t : T }} ->
     {{ Γ ⊢ t[σ ∘ τ] ≈ t[σ][τ] : T[σ ∘ τ] }} )
| wf_eq_var_0_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ T : Type@i }} ->
     {{ Γ ⊢ t : T[σ] }} ->
     {{ Γ ⊢ (#0)[σ ,, t] ≈ t : T[σ] }} )
| wf_eq_var_S_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ T : Type@i }} ->
     {{ Γ ⊢ t : T[σ] }} ->
     {{ #x : T ∈ Δ }} ->
     {{ Γ ⊢ (#(S x))[σ ,, t] ≈ (#x)[σ] : T[σ] }} )
| wf_eq_cumu :
  `( {{ Γ ⊢ T ≈ T' : Type@i }} ->
     {{ Γ ⊢ T ≈ T' : Type@(S i) }} )
| wf_eq_conv :
  `( {{ Γ ⊢ t ≈ t' : T }} ->
     {{ Γ ⊢ T ≈ T' : Type@i }} ->
     {{ Γ ⊢ t ≈ t' : T' }} )
| wf_eq_sym :
  `( {{ Γ ⊢ t ≈ t' : T }} ->
     {{ Γ ⊢ t' ≈ t : T }} )
| wf_eq_trans :
  `( {{ Γ ⊢ t ≈ t' : T }} ->
     {{ Γ ⊢ t' ≈ t'' : T }} ->
     {{ Γ ⊢ t ≈ t'' : T }} )
where "Γ ⊢ A ≈ B : T" := (wf_eq Γ A B T) (in custom judg) : type_scope
with wf_sub_eq : ctx -> sub -> sub -> ctx -> Prop :=
| wf_sub_eq_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ ⊢ Γ , T }} ->
     {{ Γ , T ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Γ ⊢s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ T : Type@i }} ->
     {{ Γ ⊢ t ≈ t' : T[σ] }} ->
     {{ Γ ⊢s (σ ,, t) ≈ (σ' ,, t') : Δ , T }} )
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
     {{ Γ'' ⊢ T : Type@i }} ->
     {{ Γ' ⊢ t : T[σ] }} ->
     {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ ⊢s (σ ,, t) ∘ τ ≈ ((σ ∘ τ) ,, t[τ]) : Γ'' , T }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ T : Type@i }} ->
     {{ Γ' ⊢ t : T[σ] }} ->
     {{ Γ' ⊢s Wk ∘ (σ ,, t) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ , T }} ->
     {{ Γ' ⊢s σ ≈ ((Wk ∘ σ) ,, (#0)[σ]) : Γ , T }} )
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
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ S1 S2 Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_exp wf_sub wf_eq wf_sub_eq ctx_lookup: mcltt.
