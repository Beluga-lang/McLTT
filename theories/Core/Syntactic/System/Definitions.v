From Coq Require Import List Classes.RelationClasses.
Require Import Setoid Morphisms.
From Mcltt Require Import Base LibTactics.
From Mcltt Require Export Syntax.
Import Syntax_Notations.

Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "⊢ Γ ≈ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢s σ ≈ σ' : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Reserved Notation "⊢ Γ ⊆ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢ A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
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

with wf_ctx_sub : ctx -> ctx -> Prop :=
| wf_ctx_sub_empty : {{ ⊢ ⋅ ⊆ ⋅ }}
| wf_ctx_sub_extend :
  `( {{ ⊢ Γ ⊆ Δ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Δ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ ⊢ Γ , A ⊆ Δ , A' }} )
where "⊢ Γ ⊆ Γ'" := (wf_ctx_sub Γ Γ') (in custom judg) : type_scope

with wf_exp : ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Type@i : Type@(S i) }} )
| wf_nat :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ ℕ : Type@0 }} )
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
| wf_exp_subtyp :
  `( {{ Γ ⊢ M : A }} ->
     (** We have this extra argument for soundness.
         Note that we need to keep it asymmetric:
         only [A'] is checked. If we check A as well,
         we cannot even construct something like
         [{{ Γ ⊢ Type@0[Wk] : Type@1 }}] with the current
         rules. Under the symmetric rule, the example requires
         [{{ Γ ⊢ Type@1[Wk] : Type@2 }}] to apply [wf_exp_sub],
         which requires [{{ Γ ⊢ Type@2[Wk] : Type@3 }}], and so on.
      *)
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ ⊢ M : A' }} )
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

with wf_sub : ctx -> ctx -> sub -> Prop :=
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
| wf_sub_subtyp :
  `( {{ Γ ⊢s σ : Δ }} ->
     (** As in [wf_exp_subtyp], this extra argument is
         for soundness. We don't need to keep it asymmetric,
         but do so to match with [wf_exp_subtyp].
      *)
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ ⊢s σ : Δ' }} )
where "Γ ⊢s σ : Δ" := (wf_sub Γ Δ σ) (in custom judg) : type_scope

with wf_exp_eq : ctx -> typ -> exp -> exp -> Prop :=
| wf_exp_eq_typ_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@(S i) }} )
| wf_exp_eq_nat_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@0 }} )
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
| wf_exp_eq_subtyp :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     (** This extra argument is here to be consistent with
         [wf_exp_subtyp].
      *)
     {{ Γ ⊢ A ⊆ A' }} ->
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
| wf_sub_eq_subtyp :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     (** This extra argument is here to be consistent with
         [wf_sub_subtyp].
      *)
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ' }} )
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ Δ S1 S2) (in custom judg) : type_scope

with wf_subtyp : ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the lemmas
      in CtxSub.v independently. We can prove those and
      presupposition lemmas mutually dependently, but that would
      be more messy.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( {{ Γ ⊢ M' : Type@i }} ->
     {{ Γ ⊢ M ≈ M' : Type@i }} ->
     {{ Γ ⊢ M ⊆ M' }} )
| wf_subtyp_trans :
  `( {{ Γ ⊢ M ⊆ M' }} ->
     {{ Γ ⊢ M' ⊆ M'' }} ->
     {{ Γ ⊢ M ⊆ M'' }} )
| wf_subtyp_univ :
  `( {{ ⊢ Γ }} ->
     i < j ->
     {{ Γ ⊢ Type@i ⊆ Type@j }} )
| wf_subtyp_pi :
  `( {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Γ , A ⊢ B : Type@i }} ->
     {{ Γ , A' ⊢ B' : Type@i }} ->
     {{ Γ , A' ⊢ B ⊆ B' }} ->
     {{ Γ ⊢ Π A B ⊆ Π A' B' }} )
where "Γ ⊢ A ⊆ A'" := (wf_subtyp Γ A A') (in custom judg) : type_scope.

Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_sub_mut_ind := Induction for wf_ctx_sub Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop
with wf_subtyp_mut_ind := Induction for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_ctx_sub_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind,
  wf_subtyp_mut_ind.

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_sub_mut_ind'.

Inductive wf_ctx_eq : ctx -> ctx -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ⊢ A ≈ A' : Type@i }} ->
     {{ ⊢ Γ , A ≈ Δ , A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_ctx_sub wf_exp wf_sub wf_exp_eq wf_sub_eq wf_subtyp ctx_lookup : mcltt.

#[export]
Instance wf_exp_eq_PER Γ A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_PER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_ctx_eq_Symmetric : Symmetric wf_ctx_eq.
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_subtyp_Transitive Γ : Transitive (wf_subtyp Γ).
Proof.
  hnf; mauto.
Qed.

(** Immediate & Independent Presuppositions *)

Lemma presup_ctx_sub : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_ctx_sub : mcltt.

Lemma presup_ctx_sub_left : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_left : mcltt.

Lemma presup_ctx_sub_right : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_right : mcltt.

Lemma presup_subtyp_right : forall {Γ A B}, {{ Γ ⊢ A ⊆ B }} -> exists i, {{ Γ ⊢ B : Type@i }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_right : mcltt.

(** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Γ A A' M,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mcltt.
#[export]
Remove Hints wf_exp_subtyp : mcltt.

Lemma wf_sub_subtyp' : forall Γ Δ Δ' σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_subtyp' : mcltt.
#[export]
Remove Hints wf_sub_subtyp : mcltt.

Lemma wf_exp_eq_subtyp' : forall Γ A A' M M',
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mcltt.
#[export]
Remove Hints wf_exp_eq_subtyp : mcltt.

Lemma wf_sub_eq_subtyp' : forall Γ Δ Δ' σ σ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_subtyp' : mcltt.
#[export]
Remove Hints wf_sub_eq_subtyp : mcltt.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature eq ==> wf_exp_eq Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature wf_sub_eq Γ Δ ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature eq ==> wf_sub_eq Γ Δ ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub wf_exp_eq_nat_sub using mauto 3 : mcltt.

#[export]
Hint Rewrite -> wf_sub_eq_id_compose_right wf_sub_eq_id_compose_left
                  wf_sub_eq_compose_assoc (* prefer right association *)
                  wf_sub_eq_p_extend using mauto 4 : mcltt.

#[export]
Hint Rewrite -> wf_exp_eq_sub_id wf_exp_eq_pi_sub using mauto 4 : mcltt.

#[export]
Instance wf_exp_eq_per_elem Γ T : PERElem _ (wf_exp Γ T) (wf_exp_eq Γ T).
Proof.
  intros a Ha. mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem Γ Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros a Ha. mauto.
Qed.
