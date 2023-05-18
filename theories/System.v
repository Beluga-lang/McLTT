Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.

Reserved Notation "⊢ Γ" (at level 80).
Reserved Notation "⊢ Γ ≈ Δ" (at level 80, Γ at next level, Δ at next level).
Reserved Notation "Γ ⊢ A ≈ B : T" (at level 80, A at next level, B at next level).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).
Reserved Notation "Γ ⊢s σ : Δ" (no associativity, at level 80, σ at next level).
Reserved Notation "Γ ⊢s S1 ≈ S2 : Δ" (no associativity, at level 80, S1 at next level, S2 at next level).
Reserved Notation "x : T ∈! Γ" (no associativity, at level 80). 

Generalizable All Variables.


Inductive ctx_lookup : nat -> Typ -> Ctx -> Prop :=
  | here : `( 0 :  (a_sub T a_weaken) ∈! (T :: Γ))
  | there : `( n : T ∈! Γ -> (S n) : (a_sub T a_weaken) ∈! (T' :: Γ))              
where "x : T ∈! Γ" := (ctx_lookup x T Γ).


Inductive wf_ctx : Ctx -> Prop :=
  | wf_empty : ⊢ []
  | wf_extend : `(
      ⊢ Γ ->
      Γ ⊢ T : typ i ->
      ⊢ T :: Γ
    ) 
where "⊢ Γ" := (wf_ctx Γ)
with wf_ctx_eq : Ctx -> Ctx -> Prop :=
  | wfc_empty : ⊢ [] ≈ []
  | wfc_extend : `(
      ⊢ Γ ≈ Δ ->
      Γ ⊢ T : typ i ->
      Δ ⊢ T' : typ i ->
      Γ ⊢ T ≈ T' : (typ i) ->
      Δ ⊢ T ≈ T' : (typ i) ->
      ⊢ (T :: Γ) ≈ (T' :: Δ)
    ) 
where "⊢ Γ ≈ Δ" := (wf_ctx_eq Γ Δ)
with wf_term : Ctx -> exp -> Typ -> Prop :=
  | wf_univ_nat_f :
      `(⊢ Γ -> Γ ⊢ ℕ : typ i)
  | wf_univ :
      `(⊢ Γ -> Γ ⊢ typ i : typ (i + 1))
  | wf_univ_fun_f : `(
      Γ ⊢ a : typ i ->
      a :: Γ ⊢ b : typ i ->
      Γ ⊢ 𝝺 a b : typ i
    )
  | wf_pi : `(
      Γ ⊢ A : typ i ->
      A :: Γ ⊢ B : typ i ->
      Γ ⊢ Π A B : typ i
    )
  | wf_vlookup : `(
      ⊢ Γ ->
      x : T ∈! Γ ->
      Γ ⊢ a_var x : T
    )
| wf_fun_e: `(
      Γ ⊢ A : typ i ->          
      A :: Γ ⊢ B : typ i ->            
      Γ ⊢ M : Π A B ->
      Γ ⊢ N : A ->
      Γ ⊢ a_app M N : a_sub B (a_id ,, N)
    )
  | wf_fun_i : `(
      Γ ⊢ A : typ i ->
      A :: Γ ⊢ M : B ->
      Γ ⊢ 𝝺 A M : Π A B
    )
  | wf_zero :
      `(⊢ Γ -> Γ ⊢ a_zero : ℕ)
  | wf_succ :
      `(Γ ⊢ n : ℕ -> Γ ⊢ a_succ n : ℕ)
  | wf_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ M : A ->
      Γ ⊢ a_sub M σ : a_sub A σ
               )
  | wf_conv : `(
      Γ ⊢ t : T ->
      (Γ ⊢ T ≈ T' : (typ i)) ->
      Γ ⊢ t : T'
      ) 
  | wf_cumu :
      `(Γ ⊢ T : typ i -> Γ ⊢ T : typ (1 + i))   
where "Γ ⊢ t : T" := (wf_term Γ t T)
with wf_sb : Ctx -> Sb -> Ctx -> Prop :=
  | wf_sb_id :
      `(⊢ Γ -> Γ ⊢s a_id : Γ)
  | wf_sb_weaken : `(
      ⊢ A :: Γ ->
      A :: Γ ⊢s a_weaken : Γ
    )
  | wf_sb_compose : `(
      Γ1 ⊢s σ2 : Γ2 ->
      Γ2 ⊢s σ1 : Γ3 ->
      Γ1 ⊢s σ1 ∙ σ2 : Γ3
    )
  | wf_sb_extend : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ A : typ i ->
      Γ ⊢ M : a_sub A σ ->
      Γ ⊢s (σ ,, M) : A :: Δ
     )
  | wf_sb_conv : `(
      Γ ⊢s σ : Δ ->
      ⊢ Δ ≈ Δ' ->                        
      Γ ⊢s σ : Δ'
     )  
where "Γ ⊢s σ : Δ" := (wf_sb Γ σ Δ)
with wf_term_eq : Ctx -> exp -> exp -> Typ -> Prop :=
  | wf_eq_nat_sub :
      `(Γ ⊢s σ : Δ -> Γ ⊢ (a_sub ℕ σ) ≈ ℕ : typ i)
  | wf_eq_typ_sub :
      `(Γ ⊢s σ : Δ -> Γ ⊢ a_sub (typ i) σ ≈ typ i : typ (i+1))
  | wf_eq_pi_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T' : typ i ->
      T' :: Δ ⊢ T : typ i ->
      Γ ⊢ a_sub (Π T' T) σ ≈ Π (a_sub T' σ) (a_sub T σ) : typ i
    )                             
  | wf_eq_pi_cong : `(
      Γ ⊢ T : typ i ->
      Γ ⊢ M ≈ M' : typ i ->         
      M :: Γ ⊢ T ≈ T' : typ i ->              
      Γ ⊢ Π M T ≈ Π M' T' : typ i              
    )
  | wf_eq_var : `(
      ⊢ Γ ->
      x : T ∈! Γ ->
      Γ ⊢ a_var x ≈ a_var x : T
   )   
  | wf_eq_zero :
      `(⊢ Γ -> Γ ⊢ a_zero ≈ a_zero : ℕ)
  | wf_eq_zero_sub :
      `(Γ ⊢s σ : Δ  -> Γ ⊢ a_sub a_zero σ ≈ a_zero : ℕ)
  | wf_eq_succ :
      `(Γ ⊢ t ≈ t' : ℕ -> Γ ⊢ a_succ t ≈ a_succ t' : ℕ)
  | wf_eq_succ_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ t : ℕ ->            
      Γ ⊢ a_sub (a_succ t) σ ≈ a_succ (a_sub t σ) : ℕ
    )
  | wf_eq_sub_cong : `(
      Δ ⊢ t ≈ t' : T ->
      Γ ⊢s σ ≈ σ' : Δ ->
      Γ ⊢ a_sub t σ ≈ a_sub t' σ' : a_sub T σ
    )
  | wf_eq_sub_id :
      `(Γ ⊢ t : T -> Γ ⊢ a_sub t a_id ≈ t : T)
  | wf_eq_sub_weak : `(
      ⊢ M :: Γ ->
      x : T ∈! Γ ->
      M :: Γ ⊢ a_sub (a_var x) a_weaken ≈ a_var (S x) : a_sub T a_weaken 
   )   
  | wf_eq_sub_comp : `(
      Γ ⊢s τ : Γ' ->
      Γ' ⊢s σ : Γ'' -> 
      Γ'' ⊢ t : T -> 
      Γ ⊢ a_sub t (σ ∙ τ) ≈ a_sub (a_sub t σ) τ : a_sub T (σ ∙ τ) 
    )
  | wf_eq_var_ze : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T : typ i ->          
      Γ ⊢ t : a_sub T σ ->          
      Γ ⊢ a_sub (a_var 0) (σ ,, t) ≈ t : a_sub T σ        
    )
  | wf_eq_var_su : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T : typ i ->          
      Γ ⊢ t : a_sub T σ ->         
      x : T ∈! Δ ->  
      Γ ⊢ a_sub (a_var (S x)) (σ ,, t) ≈ a_sub (a_var x) σ : a_sub T σ           
    )   
  | wf_eq_cumu : 
      `(Γ ⊢ T ≈ T' : typ i ->Γ ⊢ T ≈ T' : typ (1+i))   
  | wf_eq_conv : `(
      Γ ⊢ t ≈ t' : T ->
      Γ ⊢ T ≈ T' : typ i ->              
      Γ ⊢ t ≈ t' : T'            
    )
  | wf_eq_sym :
      `(Γ ⊢ t ≈ t' : T -> Γ ⊢ t' ≈ t : T)
  | wf_eq_trans : `(
      Γ ⊢ t ≈ t' : T ->
      Γ ⊢ t' ≈ t'' : T ->            
      Γ ⊢ t ≈ t'' : T             
    )   
where "Γ ⊢ A ≈ B : T" := (wf_term_eq Γ A B T)
with wf_sub_eq : Ctx -> Sb -> Sb -> Ctx -> Prop :=
  | wf_sub_eq_id :
      `(⊢ Γ -> Γ ⊢s a_id ≈ a_id : Γ)
  | wf_sub_eq_wk :
      `(⊢ T :: Γ -> T :: Γ ⊢s a_weaken ≈ a_weaken : Γ)
  | wf_sub_eq_comp_cong : `(
      Γ ⊢s τ ≈ τ' : Γ' ->
      Γ' ⊢s σ ≈ σ' : Γ'' ->
      Γ ⊢s σ ∙ τ ≈ σ' ∙ τ' : Γ''
    )                             
  | wf_sub_eq_ext_cong : `(
      Γ ⊢s σ ≈ σ' : Δ ->
      Δ ⊢ T : typ i ->  
      Γ ⊢ t ≈ t' : a_sub T σ ->        
      Γ ⊢s (σ ,, t) ≈ (σ' ,, t') : T :: Δ             
    )   
  | wf_sub_eq_id_comp_right :
      `(Γ ⊢s σ : Δ -> Γ ⊢s a_id ∙ σ ≈ σ : Δ)   
  | wf_sub_eq_id_comp_left :
      `(Γ ⊢s σ : Δ -> Γ ⊢s σ ∙ a_id ≈ σ : Δ)   
  | wf_sub_eq_comp_assoc : `(
      Γ' ⊢s σ : Γ ->   
      Γ'' ⊢s σ' : Γ' ->   
      Γ''' ⊢s σ'' : Γ'' ->   
      Γ''' ⊢s (σ ∙ σ') ∙ σ'' ≈ σ ∙ (σ' ∙ σ'') : Γ
    )
  | wf_sub_eq_ext_comp : `(
      Γ' ⊢s σ : Γ'' ->
      Γ'' ⊢ T : typ i ->           
      Γ' ⊢ t : a_sub T σ ->         
      Γ ⊢s τ : Γ' ->           
      Γ ⊢s (σ ,, t) ∙ τ ≈ ((σ ∙ τ) ,, (a_sub t τ)) : T :: Γ''            
    )             
  | wf_sub_eq_p_ext : `(
      Γ' ⊢s σ : Γ ->
      Γ ⊢ T : typ i ->           
      Γ' ⊢ t : a_sub T σ ->         
      Γ' ⊢s a_weaken ∙ (σ ,, t) ≈ σ : Γ           
    )   
  | wf_sub_eq_ext : `(
      Γ ⊢s σ : T :: Γ ->
      Γ ⊢s σ ≈ ((a_weaken ∙ σ) ,, (a_sub (a_var 0) σ)) : T :: Γ                    
    )   
  | wf_sub_eq_sym :
      `(Γ ⊢s σ ≈ σ' : Δ -> Γ ⊢s σ' ≈ σ : Δ)  
  | wf_sub_eq_trans : `(
      Γ ⊢s σ ≈ σ' : Δ ->
      Γ ⊢s σ' ≈ σ'' : Δ ->            
      Γ ⊢s σ ≈ σ'' : Δ
    )                                   
  | wf_sub_eq_conv: `(
      Γ ⊢s σ ≈ σ' : Δ ->
      ⊢ Δ ≈ Δ' ->               
      Γ ⊢s σ ≈ σ' : Δ'  
   )   
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ S1 S2 Δ).


#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_term wf_sb wf_term_eq wf_sub_eq: mcltt.
