Require Import Unicode.Utf8_core.
Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.CtxEqLemmas.
Require Import Mcltt.LibTactics.
Require Import Mcltt.CtxEquiv.
Require Import Mcltt.PresupLemmas.
Require Import Setoid.
Require Import Coq.Program.Equality.



Lemma ctx_eq_refl (Γ : Ctx) : ⊢ Γ ->  ⊢ Γ ≈ Γ.
Proof.
  intro.
  induction H;mauto.
Qed.

Lemma ctx_eq_trans (Γ Δ Δ' : Ctx) : ⊢ Γ ≈ Δ -> ⊢ Δ ≈ Δ' -> ⊢ Γ ≈ Δ'.
Proof.
  intros.
  generalize dependent Δ'.
  induction H.
  - intros.
    auto.
  - intros.
    inversion H4.
    destruct (lift_tm_max _ _ _ _ i i0 H0 H9).
    destruct (lift_eq_max _ _ _ _ _ _ i i0 H2 H10).
    destruct (lift_eq_max _ _ _ _ _ _ i i0 H3 H12).
    econstructor;mauto. 
Qed.

Definition rel_tm (Γ : Ctx) (T : Typ) (t : exp) : Prop := (wf_term Γ t T).
Definition rel_sb (Γ Δ: Ctx) (σ : Sb) : Prop := (wf_sb Γ σ Δ).

Definition term_eq (Γ : Ctx) (T : Typ) (t t' : exp) : Prop := (wf_term_eq Γ t t' T).
Definition sb_eq (Γ Δ : Ctx) (σ σ' : Sb) : Prop := (wf_sub_eq Γ σ σ' Δ).




Lemma wf_to_term_eq (Γ : Ctx) (T : Typ) (t t' : exp) : wf_term_eq Γ t t' T -> term_eq Γ T t t'.
Proof.
  intros;auto.
Qed.  

Lemma wf_to_sb_eq (Γ Δ : Ctx) (σ σ' : Sb) : wf_sub_eq Γ σ σ' Δ -> sb_eq Γ Δ σ σ'.
Proof.
  intros;auto.
Qed.  

Lemma term_eq_to_wf (Γ : Ctx) (T : Typ) (t t' : exp) : term_eq Γ T t t'-> wf_term_eq Γ t t' T.
Proof.
  intros;auto.
Qed.  
  
Lemma sb_eq_to_wf (Γ Δ : Ctx) (σ σ' : Sb) : sb_eq Γ Δ σ σ' -> wf_sub_eq Γ σ σ' Δ .
Proof.
  intros;auto.
Qed.

Lemma rel_tm_to_wf_term (Γ : Ctx) (T : Typ) (t : exp) : rel_tm Γ T t -> Γ ⊢ t : T .
Proof.
  auto.
Qed.

Lemma rel_sb_to_wf_sub (Γ Δ : Ctx) (σ : Sb) : rel_sb Γ Δ σ -> Γ ⊢s σ : Δ.
Proof.
  auto.
Qed.

Lemma wf_term_to_rel_tm (Γ : Ctx) (T : Typ) (t : exp) : Γ ⊢ t : T -> rel_tm Γ T t.
Proof.
  auto.
Qed.

Lemma wf_sb_to_rel_sb (Γ Δ : Ctx) (σ : Sb) : Γ ⊢s σ : Δ -> rel_sb Γ Δ σ.
Proof.
  auto.
Qed.
  
Lemma tm_symmetry (Γ : Ctx) (T : Typ) (t t' : exp) : term_eq Γ T t t' -> term_eq Γ T t' t.
Proof.
  intros.
  auto using term_eq_to_wf,wf_to_term_eq,wf_eq_sym.
Qed.  

Lemma tm_transitivity (Γ : Ctx) (T : Typ) (t t' t'' : exp) :  term_eq Γ T t t' -> term_eq Γ T t' t'' ->  term_eq Γ T t t''.
Proof.
  intros.
  eauto using term_eq_to_wf,wf_to_term_eq,wf_eq_trans.
Qed.

Lemma sb_symmetry (Γ Δ: Ctx) (σ σ' : Sb) : sb_eq Γ Δ σ σ' -> sb_eq Γ Δ σ' σ.
Proof.
  intros.
  auto using sb_eq_to_wf,wf_to_sb_eq,wf_sub_eq_sym.
Qed.  

Lemma sb_transitivity (Γ Δ: Ctx) (σ σ' σ'' : Sb) :  sb_eq Γ Δ σ σ' -> sb_eq Γ Δ σ' σ'' ->  sb_eq Γ Δ σ σ''.
Proof.
  intros.
  eauto using sb_eq_to_wf,wf_to_sb_eq,wf_sub_eq_trans.
Qed.  



Add Parametric Relation : (Ctx) (wf_ctx_eq)
    symmetry proved by ctx_eq_sym
    transitivity proved by ctx_eq_trans
    as ctx_eq_rel.

Add Parametric Relation (Γ : Ctx) (T : Typ) : (exp) (term_eq Γ T)
    symmetry proved by (tm_symmetry Γ T)
    transitivity proved by (tm_transitivity Γ T)
    as tm_eq_rel.                                                

Add Parametric Relation (Γ Δ : Ctx) : (Sb) (sb_eq Γ Δ)
    symmetry proved by (sb_symmetry Γ Δ)
    transitivity proved by (sb_transitivity Γ Δ)
    as sb_eq_rel.


Ltac convert_hypotheses_to_relational :=
  let rec convert:=
    match goal with
    | [H : (?Γ ⊢ ?t ≈ ?t' : ?T) |- _] => (apply wf_to_term_eq in H);convert
    | [H : (?Γ ⊢s ?σ ≈ ?σ' : ?Δ) |- _] => (apply wf_to_sb_eq in H);convert
    | [H : (?Γ ⊢ ?t : ?T) |- _] => (apply wf_term_to_rel_tm in H);convert
    | [H : (?Γ ⊢s ?σ : ?Δ) |- _] => (apply wf_sb_to_rel_sb in H);convert
    | [H : _ |- _ ] => idtac
    end
  in convert
.

Ltac convert_hypotheses_to_term := let rec convert:=
    match goal with
    | [H : (term_eq ?Γ ?T ?t ?t') |- _] => (apply term_eq_to_wf in H);convert
    | [H : (sb_eq ?Γ ?Δ ?σ ?σ') |- _] => (apply sb_eq_to_wf in H);convert
    | [H : (rel_tm ?Γ ?T ?t) |- _] => (apply rel_tm_to_wf_term in H);convert
    | [H : (rel_sb ?Γ ?Δ ?t) |- _] => (apply rel_sb_to_wf_sub in H);convert
    | [H : _ |- _ ] => idtac
    end
  in convert
.


Ltac convert_to_relational :=
  (try eapply term_eq_to_wf);
  (try eapply rel_tm_to_wf_term);
  (try eapply rel_sb_to_wf_sub);
  (try eapply sb_eq_to_wf);
  convert_hypotheses_to_relational.

Ltac convert_from_relational :=
  (try eapply wf_to_term_eq);
  (try eapply wf_term_to_rel_tm);
  (try eapply wf_sb_to_rel_sb);
  (try eapply wf_to_sb_eq);
  convert_hypotheses_to_term.

Add Parametric Morphism (Γ : Ctx) (i : nat) : (term_eq Γ)
    with signature (term_eq Γ (typ i)) ==> (eq) ==> (eq) ==> (iff)
      as eq_mor.
Proof.
  intros.
  split;intros;convert_from_relational;mauto.
Qed.

Add Parametric Morphism (Γ : Ctx) (i : nat) : (rel_tm Γ) with signature (term_eq Γ (typ i)) ==> (eq) ==> (iff) as tm_mor.
Proof.
  intros.
  split;intros;convert_from_relational;mauto.
Qed.  

Add Parametric Morphism : (wf_term)
    with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==> (iff) as ctx_tm_mor.
Proof.
  intros.
  split;intros;mauto.
Qed.

Add Parametric Morphism : (wf_term_eq) with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==>(eq) ==> (iff) as ctx_eq_mor.                        
Proof.
  intros.
  split;intros;mauto.
Qed.

Add Parametric Morphism : (wf_sb) with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==> (iff) as ctx_sb_mor1.                        
Proof.  
  intros.
  split;intros;mauto.
Qed.

Add Parametric Morphism : (wf_sb) with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==> (iff) as ctx_sb_mor2.                        
Proof.  
  intros.
  split;intros;mauto.
Qed.

Add Parametric Morphism : (wf_sub_eq) with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==> (eq)==> (iff) as ctx_sb_eq_mor1.
Proof.  
  intros.
  split;intros;mauto.
Qed.

Add Parametric Morphism : (wf_sub_eq) with signature (wf_ctx_eq) ==> (eq) ==> (eq) ==> (eq)==> (iff) as ctx_sb_eq_mor2.
Proof.  
  intros.
  split;intros;mauto.
Qed.


Generalizable All Variables.


Lemma rew_tm_nat_sub : `(rel_sb Γ Δ σ -> term_eq Γ (typ i) (ℕ ⟦ σ ⟧) (ℕ)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_tm_typ_sub : `(rel_sb Γ Δ σ ->term_eq Γ (typ (i+1)) (typ i ⟦ σ ⟧) (typ i)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.


Lemma rew_tm_pi_sub : `(rel_sb Γ Δ σ -> rel_tm Δ (typ i) T' -> rel_tm (T' :: Δ) (typ i) T -> term_eq Γ (typ i) ((Π T' T) ⟦ σ ⟧)  (Π (T' ⟦ σ ⟧) (T ⟦var_wk σ ⟧))).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.


Lemma rew_tm_zero_sub : `(rel_sb Γ Δ σ -> term_eq Γ (ℕ) (a_zero ⟦ σ ⟧) (a_zero)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_tm_succ_sub : `(rel_sb Γ Δ σ -> rel_tm Δ ℕ t -> term_eq Γ (ℕ) ((a_succ t) ⟦ σ ⟧) (a_succ (t ⟦ σ ⟧))).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_tm_sub_cong : `(term_eq Δ T t t' -> sb_eq Γ Δ σ σ' -> term_eq Γ (T ⟦ σ ⟧) (t ⟦ σ ⟧) (t' ⟦ σ ⟧)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_tm_sub_comp : `(rel_sb Γ Γ' τ -> rel_sb Γ' Γ'' σ -> rel_tm Γ'' T t -> term_eq Γ (T ⟦ (σ ∙ τ) ⟧) (t ⟦ σ ∙ τ ⟧) ((t ⟦ σ ⟧) ⟦ τ ⟧)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_tm_conv : `(term_eq Γ T t t' -> term_eq Γ (typ i) T T' -> term_eq Γ T' t t').
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_sb_comp_cong : `(sb_eq Γ Γ' τ τ' -> sb_eq Γ' Γ'' σ σ' -> sb_eq Γ Γ'' (σ ∙ τ) (σ' ∙ τ')).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_sb_ext_cong : `(sb_eq Γ Δ σ σ' -> rel_tm Δ (typ i) T -> term_eq Γ (T ⟦ σ ⟧) t t' -> sb_eq Γ (T :: Δ) (σ ,, t) (σ ,, t')).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_sb_eq_id_r : `(rel_sb Γ Δ σ -> sb_eq Γ Δ (a_id ∙ σ) (σ)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.  

Lemma rew_sb_eq_id_l : `(rel_sb Γ Δ σ -> sb_eq Γ Δ (σ ∙ a_id) (σ)).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.

Lemma rew_sb_comp_assoc : `(rel_sb Γ' Γ σ -> rel_sb Γ'' Γ' σ' -> rel_sb Γ''' Γ'' σ'' -> sb_eq Γ''' Γ ((σ ∙ σ') ∙ σ'') (σ ∙ (σ' ∙ σ''))).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.       

Lemma rew_sb_ext_comp : `(rel_sb Γ' Γ'' σ -> rel_tm Γ'' (typ i) T -> rel_tm Γ' (T ⟦ σ ⟧) (t) -> rel_sb Γ Γ' τ -> sb_eq Γ (T :: Γ'') ((σ ,, t) ∙ τ) ((σ ∙ τ) ,, (a_sub t τ))).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.  

Lemma rew_sb_p_ext : `(rel_sb Γ' Γ σ -> rel_tm Γ (typ i) T -> rel_tm Γ' (T ⟦ σ ⟧) t -> sb_eq Γ' Γ (sb_proj (σ ,, t)) σ).
Proof.
  intros.
  convert_from_relational;mauto.
Qed.    

Lemma rew_sb_ext : `(rel_sb Γ' (T :: Γ) σ -> sb_eq Γ' (T :: Γ) σ (sb_proj σ ,, (a_var 0 ⟦ σ ⟧))). 
Proof.
  intros.
  convert_from_relational;mauto.
Qed. 

(*Rewrite rules for types*)
#[export]
Hint Rewrite rew_tm_nat_sub rew_tm_pi_sub rew_tm_typ_sub rew_tm_conv using mauto : mcltt_types.
(*Rewrite rules for terms*)
#[export]
Hint Rewrite rew_tm_sub_comp rew_tm_sub_cong rew_tm_succ_sub rew_tm_zero_sub using mauto: mcltt_terms.
(*Rewrite rules for extension subs*)
#[export]
Hint Rewrite rew_sb_ext rew_sb_ext_comp rew_sb_ext_cong rew_sb_p_ext using mauto : mcltt_sub_ext. 
(*Rewrite rules for substition algebra*) 
#[export]
  Hint Rewrite rew_sb_comp_assoc rew_sb_comp_cong rew_sb_eq_id_l rew_sb_eq_id_r using mauto : mcltt_sub_alg.

#[export]
Hint Rewrite rew_sb_ext rew_sb_ext_comp rew_sb_ext_cong rew_sb_p_ext rew_sb_comp_assoc rew_sb_comp_cong rew_sb_eq_id_l rew_sb_eq_id_r : mcltt_sub. 
(*Rewrite rules for types*)
#[export]
Hint Rewrite rew_tm_nat_sub rew_tm_pi_sub rew_tm_typ_sub rew_tm_conv rew_tm_sub_comp rew_tm_sub_cong rew_tm_succ_sub rew_tm_zero_sub rew_sb_ext rew_sb_ext_comp rew_sb_ext_cong rew_sb_p_ext rew_sb_comp_assoc rew_sb_comp_cong rew_sb_eq_id_l rew_sb_eq_id_r : mcltt.

Lemma test (Γ : Ctx) : ⊢ Γ -> Γ ⊢ a_zero ⟦ a_id ∙ a_id ⟧ ≈ a_zero : ℕ.
Proof.
  intro.
  convert_to_relational.
  autorewrite with mcltt_terms.
  eapply tm_eq_refl;mauto.
  convert_from_relational.
  econstructor;mauto.
Qed.  
