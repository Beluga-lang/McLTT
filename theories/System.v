Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.

Reserved Notation "⊢ Γ" (at level 80).
Reserved Notation "⊢ Γ ≈ Δ" (at level 70).
Reserved Notation "Γ ⊢ A ≈ B : T" (at level 80, A at next level, B at next level).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).
Reserved Notation "Γ ⊢ [ e ] : T" (no associativity, at level 80, e at next level).
Reserved Notation "Γ ⊢s S1 ≈ S2 : Δ" (no associativity, at level 80, S1 at next level, S2 at next level).

Generalizable All Variables.

Inductive wf_ctx : Ctx -> Set :=
  | wf_empty : ⊢ []
  | wf_extend : `(
      ⊢ Γ ->
      Γ ⊢ T : typ i ->
      ⊢ T :: Γ
    ) 
where "⊢ Γ" := (wf_ctx Γ)
with wf_ctx_eq : Ctx -> Ctx -> Set :=
  | wfc_empty : wf_ctx_eq [] []
  | wfc_extend : `(
      wf_ctx_eq Γ Δ ->
      Γ ⊢ T : typ i ->
      Δ ⊢ T' : typ i ->
      Γ ⊢ T' : typ i ->
      Γ ⊢ T ≈ T' : (typ i) ->
      Δ ⊢ T ≈ T' : (typ i) ->
      wf_ctx_eq (T :: Γ) (T' :: Δ)
    ) 
where "⊢ Γ ≈ Δ" := (wf_ctx_eq Γ Δ)
with wf_term : Ctx -> exp -> Typ -> Set :=
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
      A :: Γ ⊢ B : typ (i + 1) ->
      Γ ⊢ Π A B : typ (i + 1)
    )
  | wf_hyp : `(
      ⊢ t :: Γ ->
      t :: Γ ⊢ a_var i : (a_sub t a_weaken)
    )
  | wf_fun_e: `(
      Γ ⊢ M : Π A B ->
      Γ ⊢ N : A ->
      A :: Γ ⊢ B : typ i ->
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
      Γ ⊢ [s] : Δ ->
      Δ ⊢ M : A ->
      Γ ⊢ a_sub M s : a_sub A s
               )
  (*| wf_conv : `(
      Γ ⊢ t : T ->
      wf_context_eq T T' ->
      Γ ⊢ t : T'
      ) *)
  | wf_cumu :
      `(Γ ⊢ T : typ i -> Γ ⊢ T : typ (1 + i))   
where "Γ ⊢ t : T" := (wf_term Γ t T)
with wf_sb : Ctx -> Sb -> Ctx -> Set :=
  | wf_sb_id :
      `(⊢ Γ -> Γ ⊢ [a_id] : Γ)
  | wf_sb_weaken : `(
      Γ ⊢ A : typ i ->
      A :: Γ ⊢ [a_weaken] : Γ
    )
  | wf_sb_compose : `(
      Γ1 ⊢ [s2] : Γ2 ->
      Γ2 ⊢ [s1] : Γ3 ->
      Γ1 ⊢ [s1 -∘- s2] : Γ3
    )
  | wf_sb_extend : `(
      Γ ⊢ [s] : Δ ->
      Δ ⊢ A : typ i ->
      Γ ⊢ M : a_sub A s ->
      Γ ⊢ [s ,, M] : A :: Δ
     )
  (*| wf_sb_conv : `(
      Γ ⊢ [s] : Δ ->
      wf_contex_eq Δ Δ' ->                        
      Γ ⊢ [s] : Δ'
     )*)  
where "Γ ⊢ [ e ] : Δ" := (wf_sb Γ e Δ)
with wf_term_eq : Ctx -> exp -> exp -> Typ -> Set :=
  | wf_eq_nat_sub :
      `(Γ ⊢ [s] : Δ -> Γ ⊢ (a_sub ℕ s) ≈ ℕ : typ i)
  | wf_eq_typ_sub :
      `(Γ ⊢ [s] : Δ -> Γ ⊢ a_sub (typ i) s ≈ typ i : typ (i+1))
  | wf_eq_pi_sub : `(
      Γ ⊢ [s] : Δ ->
      Δ ⊢ T' : typ i ->
      T' :: Δ ⊢ T : typ i ->
      Γ ⊢ a_sub (Π T' T) s ≈ Π (a_sub T' s) (a_sub T s) : typ i
    )                             
  | wf_eq_pi_cong : `(
      Γ ⊢ T : typ i ->
      Γ ⊢ M ≈ M' : typ i ->         
      M :: Γ ⊢ T ≈ T' : typ i ->              
      Γ ⊢ Π M T ≈ Π M' T' : typ i              
    )
  | wf_eq_var : `(
      ⊢ a_var i :: Γ ->
      a_var i :: Γ ⊢ a_var i : T ->
      a_var i :: Γ ⊢ a_var i ≈ a_var i : T
   )   
  | wf_eq_zero :
      `(⊢ Γ -> Γ ⊢ a_zero ≈ a_zero : ℕ)
  | wf_eq_zero_sub :
      `(Γ ⊢ [σ] : Δ  -> Γ ⊢ a_sub a_zero σ ≈ a_zero : ℕ)
  | wf_eq_succ :
      `(Γ ⊢ t ≈ t' : ℕ -> Γ ⊢ a_succ t ≈ a_succ t' : ℕ)
  | wf_eq_succ_sub : `(
      Γ ⊢ [σ] : Δ ->
      Δ ⊢ t : ℕ ->            
      Γ ⊢ a_sub (a_succ t) σ ≈ a_succ (a_sub t σ) : ℕ
    )
  | wf_eq_sub_cong : `(
      Δ ⊢ t ≈ t' : T ->
      Γ ⊢s s ≈ s' : Δ ->
      Γ ⊢ a_sub t s ≈ a_sub t' s' : a_sub T s
    )
  | wf_eq_sub_id :
      `(Γ ⊢ t : T -> Γ ⊢ a_sub t a_id ≈ t : T)
  | wf_eq_sub_weak : `(
      ⊢ M :: (a_var i) :: Γ ->
      a_var i :: Γ ⊢ a_var i : T ->
      M :: a_var i :: Γ ⊢ a_sub (a_var i) a_weaken ≈ a_var (S x) : a_sub T a_weaken 
   )   
  | wf_eq_sub_comp : `(
      Γ ⊢ [τ] : Γ' ->
      Γ' ⊢ [σ] : Γ'' -> 
      Γ'' ⊢ t : T -> 
      Γ ⊢ a_sub t (σ -∘- τ) ≈ a_sub (a_sub t σ) τ : a_sub t (σ -∘- τ) 
    )
  | wf_eq_var_ze : `(
      Γ ⊢ [σ] : Δ ->
      Δ ⊢ T : typ i ->          
      Γ ⊢ t : a_sub T σ ->          
      Γ ⊢ a_sub (a_var 0) (σ ,, t) ≈ t : a_sub T σ        
    )
  | wf_eq_var_su : `(
      Γ ⊢ [σ] : Δ ->
      (a_var i) :: Δ ⊢ T : typ i ->          
      Γ ⊢ t : a_sub T σ ->         
      (a_var i) :: Δ ⊢ (a_var i) : T ->     
      Γ ⊢ a_sub (a_var (S i)) (σ ,, t) ≈ a_sub (a_var i) σ : a_sub T σ           
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
with wf_sub_eq : Ctx -> Sb -> Sb -> Ctx -> Set :=
  | wf_sub_eq_id :
      `(⊢ Γ -> Γ ⊢s a_id ≈ a_id : Γ)
  | wf_sub_eq_wk :
      `(⊢ T :: Γ -> T :: Γ ⊢s a_weaken ≈ a_weaken : Γ)
  | wf_sub_eq_comp_cong : `(
      Γ ⊢s τ ≈ τ' : Γ' ->
      Γ' ⊢s σ ≈ σ' : Γ'' ->
      Γ ⊢s σ -∘- τ ≈ σ' -∘- τ' : Γ''
    )                             
  | wf_sub_eq_ext_cong : `(
      Γ ⊢s σ ≈ σ' : Δ ->
      Δ ⊢ T : typ i ->  
      Γ ⊢ t ≈ t' : a_sub T σ ->        
      Γ ⊢s (σ ,, t) ≈ (σ' ,, t') : T :: Δ             
    )   
  | wf_sub_eq_id_comp_right :
      `(Γ ⊢ [σ] : Δ -> Γ ⊢s a_id -∘- σ ≈ σ : Δ)   
  | wf_sub_eq_id_comp_left :
      `(Γ ⊢ [σ] : Δ -> Γ ⊢s σ -∘- a_id ≈ σ : Δ)   
  | wf_sub_eq_comp_assoc : `(
      Γ' ⊢ [σ] : Γ ->   
      Γ'' ⊢ [σ'] : Γ' ->   
      Γ''' ⊢ [σ''] : Γ'' ->   
      Γ''' ⊢s (σ -∘- σ') -∘- σ'' ≈ σ -∘- (σ' -∘- σ'') : Γ
    )
  | wf_sub_eq_ext_comp : `(
      Γ' ⊢ [σ] : Γ'' ->
      Γ'' ⊢ T : typ i ->           
      Γ' ⊢ t : a_sub T σ ->         
      Γ ⊢ [τ] : Γ' ->           
      Γ ⊢s (σ ,, t) -∘- τ ≈ ((σ -∘- τ) ,, (a_sub t τ)) : T :: Γ''            
    )             
  | wf_sub_eq_p_ext : `(
      Γ' ⊢ [σ] : Γ ->
      Γ ⊢ T : typ i ->           
      Γ' ⊢ t : a_sub T σ ->         
      Γ' ⊢s a_weaken -∘- (σ ,, t) ≈ σ : Γ           
    )   
  | wf_sub_eq_ext : `(
      Γ ⊢ [σ] : T :: Γ ->
      Γ ⊢s σ ≈ ((a_weaken -∘- σ) ,, (a_sub (a_var 0) σ)) : T :: Γ                    
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
      wf_ctx_eq Δ Δ' ->               
      Γ ⊢s σ ≈ σ' : Δ'  
   )   
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ S1 S2 Δ).
