Require Import List.
Require Import Unicode.Utf8_core.
Import ListNotations.

Require Import Mcltt.Syntax.
Require Import Mcltt.LibTactics.

Open Scope mcltt.
 
Reserved Notation "⊢ Γ" (at level 80).
Reserved Notation "⊢ Γ ≈ Δ" (at level 80, Γ at next level, Δ at next level).
Reserved Notation "Γ ⊢ A ≈ B : T" (at level 80, A at next level, B at next level).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).
Reserved Notation "Γ ⊢s σ : Δ" (no associativity, at level 80, σ at next level).
Reserved Notation "Γ ⊢s S1 ≈ S2 : Δ" (no associativity, at level 80, S1 at next level, S2 at next level).
Reserved Notation "x : T ∈! Γ" (no associativity, at level 80).



Generalizable All Variables.

(*Inductive definition for the x : T ∈ Γ judgement *)

Inductive ctx_lookup : nat -> Typ -> Ctx -> Prop :=
  | here : `( 0 : (a_sub T a_weaken) ∈! (T :: Γ))
  | there : `( n : T ∈! Γ -> (S n) : (a_sub T a_weaken) ∈! (T' :: Γ))              
where "x : T ∈! Γ" := (ctx_lookup x T Γ) : mcltt.

(* Well formed contexts, well formed terms, well formed substitions and well formed equalities between them are defined by mutual induction *)
Inductive wf_ctx : Ctx -> Prop :=
  | wf_empty : ⊢ []
  | wf_extend : `(
      ⊢ Γ ->
      Γ ⊢ T : typ i ->
      ⊢ T :: Γ
    ) 
where "⊢ Γ" := (wf_ctx Γ) : mcltt
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
where "⊢ Γ ≈ Δ" := (wf_ctx_eq Γ Δ) : mcltt
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
      Γ ⊢ (M $ N) : (B ⟦| N ⟧)
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
  | wf_nat_elim : `(
      ℕ :: Γ ⊢ T : typ i ->                  
      Γ ⊢ s : (T ⟦| a_zero ⟧) ->                  
      T :: ℕ :: Γ ⊢ r : (T ⟦ ((a_weaken ∙ a_weaken) ,, a_succ (a_var 1))⟧) ->       
      Γ ⊢ a_rec T s r t : (T ⟦| t⟧)        
     )                 
  | wf_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ M : A ->
      Γ ⊢ (M ⟦ σ ⟧) : (A ⟦ σ ⟧)
      )
  | wf_conv : `(
      Γ ⊢ t : T ->
      (Γ ⊢ T ≈ T' : (typ i)) ->
      Γ ⊢ t : T'
      ) 
  | wf_cumu :
      `(Γ ⊢ T : typ i -> Γ ⊢ T : typ (1 + i))   
where "Γ ⊢ t : T" := (wf_term Γ t T) : mcltt
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
      Γ ⊢ M : (A ⟦ σ ⟧) ->
      Γ ⊢s (σ ,, M) : A :: Δ
     )
  | wf_sb_conv : `(
      Γ ⊢s σ : Δ ->
      ⊢ Δ ≈ Δ' ->                        
      Γ ⊢s σ : Δ'
     )  
where "Γ ⊢s σ : Δ" := (wf_sb Γ σ Δ) : mcltt
with wf_term_eq : Ctx -> exp -> exp -> Typ -> Prop :=
  | wf_eq_nat_sub :
      `(Γ ⊢s σ : Δ -> Γ ⊢  ℕ ⟦ σ ⟧ ≈ ℕ : typ i)
  | wf_eq_typ_sub :
      `(Γ ⊢s σ : Δ -> Γ ⊢ typ i ⟦ σ ⟧ ≈ typ i : typ (i+1))
  | wf_eq_pi_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T' : typ i ->
      T' :: Δ ⊢ T : typ i ->
      Γ ⊢ (Π T' T) ⟦ σ ⟧ ≈ Π (T' ⟦ σ ⟧) (T ⟦var_wk σ ⟧) : typ i
    )                             
  | wf_eq_pi_cong : `(
      Γ ⊢ M : typ i ->
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
      `(Γ ⊢s σ : Δ  -> Γ ⊢ a_zero ⟦ σ ⟧ ≈ a_zero : ℕ)
  | wf_eq_succ :
      `(Γ ⊢ t ≈ t' : ℕ -> Γ ⊢ a_succ t ≈ a_succ t' : ℕ)
  | wf_eq_succ_sub : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ t : ℕ ->            
      Γ ⊢ a_succ t ⟦ σ ⟧ ≈ a_succ (t ⟦ σ ⟧) : ℕ
    )
  | wf_eq_rec_cong : `(
      ℕ :: Γ ⊢ T : typ i ->                     
      ℕ :: Γ ⊢ T ≈ T' : typ i ->                     
      Γ ⊢ s ≈ s' : (T ⟦| a_zero ⟧) ->                      
      T :: ℕ :: Γ ⊢ r ≈ r' :  (T ⟦ ((a_weaken ∙ a_weaken) ,, a_succ (a_var 1)) ⟧) ->
      Γ ⊢ t ≈ t' : ℕ ->                     
      Γ ⊢ a_rec T s r t ≈ a_rec T' s' r' t' : (T ⟦| t ⟧)                     
    )
  | wf_eq_rec_sub : `(
      Γ ⊢s σ : Δ ->
      ℕ :: Δ ⊢ T : typ i ->
      Δ ⊢ s : (T ⟦| a_zero ⟧) ->
      T :: ℕ :: Δ ⊢ r : (T ⟦ ((a_weaken ∙ a_weaken) ,, a_succ (a_var 1)) ⟧) ->
      Δ ⊢ t : ℕ ->                
      Γ ⊢ (a_rec T s r t) ⟦ σ ⟧ ≈ a_rec (T ⟦ var_wk σ ⟧) (s ⟦ σ ⟧) (r  ⟦var_wk (var_wk σ)⟧) (t ⟦ σ ⟧) : (T  ⟦σ ,, (t ⟦ σ ⟧)⟧)
    )
  | wf_eq_rec_beta_ze : `(                   
      ℕ :: Γ ⊢ T : typ i ->                      
      Γ ⊢ s : (T ⟦| a_zero ⟧) -> 
      T :: ℕ :: Γ ⊢ r : (T ⟦ ((a_weaken ∙ a_weaken) ,, a_succ (a_var 1))⟧) ->           
      Γ ⊢ a_rec T s r a_zero ≈ s : (T ⟦| a_zero ⟧)
    )
  | wf_eq_rec_beta_succ : `(
      ℕ :: Γ ⊢ T : typ i ->                      
      Γ ⊢ s : (T ⟦| a_zero ⟧) ->                      
      T :: ℕ :: Γ ⊢ r : (T ⟦ ((a_weaken ∙ a_weaken) ,, a_succ (a_var 1))⟧) ->                        
      Γ ⊢ t : ℕ ->
      Γ ⊢ a_rec T s r (a_succ t) ≈ (r ⟦ ((a_id ,, t) ,, a_rec T s r t) ⟧) : (T ⟦| (a_succ t) ⟧)
    )                     
  | wf_eq_lam_cong : `(
      Γ ⊢ M : typ i ->
      M :: Γ ⊢ t ≈ t' : T ->
      Γ ⊢ 𝝺 M t ≈ 𝝺 M t' : Π M T                         
    ) 
  | wf_eq_app_cong : `(
      Γ ⊢ M : typ i ->
      M :: Γ ⊢ T : typ i ->
      Γ ⊢ r ≈ r' : Π M T ->
      Γ ⊢ m ≈ m' : M ->
      Γ ⊢ (r $ m) ≈ (r' $ m') : (T ⟦| m ⟧)
    )                            
  | wf_eq_sub_cong : `(
      Δ ⊢ t ≈ t' : T ->
      Γ ⊢s σ ≈ σ' : Δ ->
      Γ ⊢ (t ⟦ σ ⟧) ≈ (t' ⟦ σ' ⟧) : (T ⟦ σ ⟧)
    )
  | wf_eq_sub_id :
      `(Γ ⊢ t : T -> Γ ⊢ t ⟦ a_id ⟧ ≈ t : T)
  | wf_eq_sub_weak : `(
      ⊢ M :: Γ ->
      x : T ∈! Γ ->
      M :: Γ ⊢  a_var x ⟦ a_weaken ⟧ ≈ a_var (S x) : (T ⟦ a_weaken ⟧) 
   )   
  | wf_eq_sub_comp : `(
      Γ ⊢s τ : Γ' ->
      Γ' ⊢s σ : Γ'' -> 
      Γ'' ⊢ t : T -> 
      Γ ⊢ (t ⟦ σ ∙ τ ⟧) ≈  ((t ⟦ σ ⟧) ⟦ τ ⟧) : (T ⟦ (σ ∙ τ) ⟧) 
    )
  | wf_eq_var_ze : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T : typ i ->          
      Γ ⊢ t : (T ⟦ σ ⟧) ->          
      Γ ⊢ a_var 0 ⟦ σ ,, t ⟧ ≈ t : (T ⟦ σ ⟧)        
    )
  | wf_eq_var_su : `(
      Γ ⊢s σ : Δ ->
      Δ ⊢ T : typ i ->          
      Γ ⊢ t : (T ⟦ σ ⟧)->         
      x : T ∈! Δ ->  
      Γ ⊢ a_var (S x) ⟦σ ,, t⟧ ≈ (a_var x ⟦ σ ⟧) : (T ⟦ σ ⟧)           
    )
  | wf_eq_sub_lam : `(
      Γ ⊢s σ : Δ ->
      M :: Δ ⊢ t : T ->
      Γ ⊢ 𝝺 M t ⟦ σ ⟧ ≈ 𝝺 (M ⟦ σ ⟧) (t  ⟦ var_wk σ ⟧) : (Π M T ⟦ σ ⟧)                     
    )                    
  | wf_eq_sub_app : `(
     Δ ⊢ M : typ i ->                    
     M :: Δ ⊢ T : typ i ->                   
     Γ ⊢s σ : Δ ->            
     Δ ⊢ r : Π M T ->            
     Δ ⊢ m : M ->            
     Γ ⊢ (r $ m) ⟦ σ ⟧ ≈ ((r ⟦ σ ⟧) $ (m ⟦ σ ⟧)) :  (T ⟦ σ ,, a_sub m σ ⟧)       
    )
  | wf_eq_lam_beta : `(
     Γ ⊢ M : typ i ->                    
     M :: Γ ⊢ T : typ i ->        
     M :: Γ ⊢ t : T ->        
     Γ ⊢ m : M ->        
     Γ ⊢ (𝝺 M t) $ m ≈  (t ⟦| m ⟧) : (T ⟦| m ⟧)            
    )
  | wf_eq_lam_eta : `(
     Γ ⊢ M : typ i ->                   
     M :: Γ ⊢ T : typ i ->                   
     Γ ⊢ t : Π M T ->                  
     Γ ⊢ t ≈ 𝝺 M ((t ⟦ a_weaken ⟧) $ (a_var 0)) : Π M T      
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
where "Γ ⊢ A ≈ B : T" := (wf_term_eq Γ A B T) : mcltt
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
      Γ' ⊢ t : (T ⟦ σ ⟧) ->         
      Γ' ⊢s sb_proj (σ ,, t) ≈ σ : Γ           
    )   
  | wf_sub_eq_ext : `(
      Γ' ⊢s σ : T :: Γ ->
      Γ' ⊢s σ ≈ (sb_proj σ ,, (a_var 0 ⟦ σ ⟧)) : T :: Γ                    
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
where "Γ ⊢s S1 ≈ S2 : Δ" := (wf_sub_eq Γ S1 S2 Δ) : mcltt.


#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_term wf_sb wf_term_eq wf_sub_eq ctx_lookup: mcltt.

Close Scope mcltt.
